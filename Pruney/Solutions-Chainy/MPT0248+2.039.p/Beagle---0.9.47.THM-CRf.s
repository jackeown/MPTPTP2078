%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   55 (  91 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 192 expanded)
%              Number of equality atoms :   48 ( 177 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_45,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_46])).

tff(c_248,plain,(
    ! [B_36,A_37] :
      ( k1_tarski(B_36) = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k1_tarski(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_257,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_49,c_248])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_45,c_257])).

tff(c_268,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_270,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_4])).

tff(c_288,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_327,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_288])).

tff(c_407,plain,(
    ! [A_50,B_51] : k4_xboole_0(k2_xboole_0(A_50,B_51),B_51) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_423,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_407])).

tff(c_441,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_270,c_423])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_441])).

tff(c_444,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_445,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_543,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_28])).

tff(c_483,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_446,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_30])).

tff(c_504,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_446])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_537,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_8])).

tff(c_900,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_911,plain,(
    ! [A_79] :
      ( k1_tarski('#skF_1') = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_900])).

tff(c_964,plain,(
    ! [A_81] :
      ( A_81 = '#skF_2'
      | k1_xboole_0 = A_81
      | ~ r1_tarski(A_81,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_911])).

tff(c_975,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_537,c_964])).

tff(c_987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_543,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.38  
% 2.60/1.38  %Foreground sorts:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Background operators:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Foreground operators:
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.38  
% 2.60/1.39  tff(f_66, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.60/1.39  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.60/1.39  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.60/1.39  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.60/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.60/1.39  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.39  tff(c_59, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.60/1.39  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.39  tff(c_45, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.60/1.39  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.39  tff(c_46, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.39  tff(c_49, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_46])).
% 2.60/1.39  tff(c_248, plain, (![B_36, A_37]: (k1_tarski(B_36)=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, k1_tarski(B_36)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.39  tff(c_257, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_49, c_248])).
% 2.60/1.39  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_45, c_257])).
% 2.60/1.39  tff(c_268, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.60/1.39  tff(c_269, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.60/1.39  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.39  tff(c_270, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_4])).
% 2.60/1.39  tff(c_288, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.39  tff(c_327, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_288])).
% 2.60/1.39  tff(c_407, plain, (![A_50, B_51]: (k4_xboole_0(k2_xboole_0(A_50, B_51), B_51)=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_423, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_327, c_407])).
% 2.60/1.39  tff(c_441, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_270, c_423])).
% 2.60/1.39  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_441])).
% 2.60/1.39  tff(c_444, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.60/1.39  tff(c_445, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.60/1.39  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.39  tff(c_543, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_28])).
% 2.60/1.39  tff(c_483, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.39  tff(c_446, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_30])).
% 2.60/1.39  tff(c_504, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_483, c_446])).
% 2.60/1.39  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.39  tff(c_537, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_504, c_8])).
% 2.60/1.39  tff(c_900, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.39  tff(c_911, plain, (![A_79]: (k1_tarski('#skF_1')=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_445, c_900])).
% 2.60/1.39  tff(c_964, plain, (![A_81]: (A_81='#skF_2' | k1_xboole_0=A_81 | ~r1_tarski(A_81, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_911])).
% 2.60/1.39  tff(c_975, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_537, c_964])).
% 2.60/1.39  tff(c_987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_543, c_975])).
% 2.60/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  Inference rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Ref     : 0
% 2.60/1.39  #Sup     : 229
% 2.60/1.39  #Fact    : 0
% 2.60/1.39  #Define  : 0
% 2.60/1.39  #Split   : 3
% 2.60/1.39  #Chain   : 0
% 2.60/1.39  #Close   : 0
% 2.60/1.39  
% 2.60/1.39  Ordering : KBO
% 2.60/1.39  
% 2.60/1.39  Simplification rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Subsume      : 2
% 2.60/1.39  #Demod        : 97
% 2.60/1.39  #Tautology    : 180
% 2.60/1.39  #SimpNegUnit  : 5
% 2.60/1.39  #BackRed      : 4
% 2.60/1.39  
% 2.60/1.39  #Partial instantiations: 0
% 2.60/1.39  #Strategies tried      : 1
% 2.60/1.39  
% 2.60/1.39  Timing (in seconds)
% 2.60/1.39  ----------------------
% 2.60/1.40  Preprocessing        : 0.30
% 2.60/1.40  Parsing              : 0.16
% 2.60/1.40  CNF conversion       : 0.02
% 2.60/1.40  Main loop            : 0.32
% 2.60/1.40  Inferencing          : 0.12
% 2.60/1.40  Reduction            : 0.12
% 2.60/1.40  Demodulation         : 0.09
% 2.60/1.40  BG Simplification    : 0.02
% 2.60/1.40  Subsumption          : 0.05
% 2.60/1.40  Abstraction          : 0.02
% 2.60/1.40  MUC search           : 0.00
% 2.60/1.40  Cooper               : 0.00
% 2.60/1.40  Total                : 0.66
% 2.60/1.40  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
