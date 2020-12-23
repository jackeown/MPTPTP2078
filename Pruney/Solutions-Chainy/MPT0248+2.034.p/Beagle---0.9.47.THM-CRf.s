%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 192 expanded)
%              Number of equality atoms :   48 ( 177 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_315,plain,(
    ! [B_40,A_41] :
      ( k1_tarski(B_40) = A_41
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_tarski(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_329,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_47,c_315])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_42,c_329])).

tff(c_339,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_340,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_341,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_4])).

tff(c_367,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_382,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_30])).

tff(c_494,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),B_56) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_510,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_494])).

tff(c_527,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_341,c_510])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_527])).

tff(c_530,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_531,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_627,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_531,c_28])).

tff(c_568,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_558,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_30])).

tff(c_589,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_558])).

tff(c_622,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_8])).

tff(c_878,plain,(
    ! [B_80,A_81] :
      ( k1_tarski(B_80) = A_81
      | k1_xboole_0 = A_81
      | ~ r1_tarski(A_81,k1_tarski(B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_889,plain,(
    ! [A_81] :
      ( k1_tarski('#skF_1') = A_81
      | k1_xboole_0 = A_81
      | ~ r1_tarski(A_81,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_878])).

tff(c_895,plain,(
    ! [A_82] :
      ( A_82 = '#skF_2'
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_889])).

tff(c_906,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_622,c_895])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_627,c_906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  
% 2.56/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.42  
% 2.56/1.42  %Foreground sorts:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Background operators:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Foreground operators:
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.42  
% 2.56/1.43  tff(f_66, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.56/1.43  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.56/1.43  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.56/1.43  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.56/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.56/1.43  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.56/1.43  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.43  tff(c_51, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.56/1.43  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.43  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.56/1.43  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.43  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.43  tff(c_47, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 2.56/1.43  tff(c_315, plain, (![B_40, A_41]: (k1_tarski(B_40)=A_41 | k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.43  tff(c_329, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_47, c_315])).
% 2.56/1.43  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_42, c_329])).
% 2.56/1.43  tff(c_339, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.56/1.43  tff(c_340, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.56/1.43  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.43  tff(c_341, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_340, c_4])).
% 2.56/1.43  tff(c_367, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.43  tff(c_382, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_367, c_30])).
% 2.56/1.43  tff(c_494, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), B_56)=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.43  tff(c_510, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_382, c_494])).
% 2.56/1.43  tff(c_527, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_341, c_510])).
% 2.56/1.43  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_527])).
% 2.56/1.43  tff(c_530, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.56/1.43  tff(c_531, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.56/1.43  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.43  tff(c_627, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_531, c_531, c_28])).
% 2.56/1.43  tff(c_568, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.43  tff(c_558, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_531, c_30])).
% 2.56/1.43  tff(c_589, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_568, c_558])).
% 2.56/1.43  tff(c_622, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_8])).
% 2.56/1.43  tff(c_878, plain, (![B_80, A_81]: (k1_tarski(B_80)=A_81 | k1_xboole_0=A_81 | ~r1_tarski(A_81, k1_tarski(B_80)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.43  tff(c_889, plain, (![A_81]: (k1_tarski('#skF_1')=A_81 | k1_xboole_0=A_81 | ~r1_tarski(A_81, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_531, c_878])).
% 2.56/1.43  tff(c_895, plain, (![A_82]: (A_82='#skF_2' | k1_xboole_0=A_82 | ~r1_tarski(A_82, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_889])).
% 2.56/1.43  tff(c_906, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_622, c_895])).
% 2.56/1.43  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_627, c_906])).
% 2.56/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.43  
% 2.56/1.43  Inference rules
% 2.56/1.43  ----------------------
% 2.56/1.43  #Ref     : 0
% 2.56/1.43  #Sup     : 218
% 2.56/1.43  #Fact    : 0
% 2.56/1.43  #Define  : 0
% 2.56/1.43  #Split   : 3
% 2.56/1.43  #Chain   : 0
% 2.56/1.43  #Close   : 0
% 2.56/1.43  
% 2.56/1.43  Ordering : KBO
% 2.56/1.43  
% 2.56/1.43  Simplification rules
% 2.56/1.43  ----------------------
% 2.56/1.43  #Subsume      : 8
% 2.56/1.43  #Demod        : 81
% 2.56/1.43  #Tautology    : 168
% 2.56/1.43  #SimpNegUnit  : 5
% 2.56/1.43  #BackRed      : 2
% 2.56/1.43  
% 2.56/1.43  #Partial instantiations: 0
% 2.56/1.43  #Strategies tried      : 1
% 2.56/1.43  
% 2.56/1.43  Timing (in seconds)
% 2.56/1.43  ----------------------
% 2.56/1.44  Preprocessing        : 0.28
% 2.56/1.44  Parsing              : 0.15
% 2.56/1.44  CNF conversion       : 0.02
% 2.56/1.44  Main loop            : 0.31
% 2.56/1.44  Inferencing          : 0.11
% 2.56/1.44  Reduction            : 0.11
% 2.56/1.44  Demodulation         : 0.08
% 2.56/1.44  BG Simplification    : 0.02
% 2.56/1.44  Subsumption          : 0.04
% 2.56/1.44  Abstraction          : 0.01
% 2.56/1.44  MUC search           : 0.00
% 2.56/1.44  Cooper               : 0.00
% 2.56/1.44  Total                : 0.61
% 2.56/1.44  Index Insertion      : 0.00
% 2.56/1.44  Index Deletion       : 0.00
% 2.56/1.44  Index Matching       : 0.00
% 2.56/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
