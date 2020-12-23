%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 128 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 291 expanded)
%              Number of equality atoms :   53 ( 243 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_45,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_45])).

tff(c_102,plain,(
    ! [B_35,A_36] :
      ( k1_tarski(B_35) = A_36
      | k1_xboole_0 = A_36
      | ~ r1_tarski(A_36,k1_tarski(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_44,c_112])).

tff(c_124,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_165,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,k2_xboole_0(C_43,B_44))
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_42,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_165])).

tff(c_125,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_204,plain,(
    ! [B_54,A_55] :
      ( k1_tarski(B_54) = A_55
      | A_55 = '#skF_2'
      | ~ r1_tarski(A_55,k1_tarski(B_54)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_16])).

tff(c_221,plain,(
    ! [A_56] :
      ( k1_tarski('#skF_1') = A_56
      | A_56 = '#skF_2'
      | ~ r1_tarski(A_56,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_171,c_204])).

tff(c_229,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_51,c_221])).

tff(c_236,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_229])).

tff(c_126,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_2') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_4])).

tff(c_241,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_3') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_126])).

tff(c_244,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_28])).

tff(c_270,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_244])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_270])).

tff(c_272,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_273,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_305,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_273,c_26])).

tff(c_296,plain,(
    ! [A_59,B_60] : r1_tarski(A_59,k2_xboole_0(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_302,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_296])).

tff(c_274,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_28])).

tff(c_336,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,k2_xboole_0(C_68,B_69))
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_339,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,'#skF_2')
      | ~ r1_tarski(A_67,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_336])).

tff(c_366,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_377,plain,(
    ! [A_78] :
      ( k1_tarski('#skF_1') = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_366])).

tff(c_383,plain,(
    ! [A_79] :
      ( A_79 = '#skF_2'
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_377])).

tff(c_404,plain,(
    ! [A_80] :
      ( A_80 = '#skF_2'
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_339,c_383])).

tff(c_412,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_302,c_404])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_305,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.31  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.31  
% 2.07/1.31  %Foreground sorts:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Background operators:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Foreground operators:
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.31  
% 2.07/1.32  tff(f_66, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.07/1.32  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.32  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.07/1.32  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.07/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.07/1.32  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.32  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.07/1.32  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.32  tff(c_44, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.07/1.32  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.32  tff(c_45, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.32  tff(c_48, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_45])).
% 2.07/1.32  tff(c_102, plain, (![B_35, A_36]: (k1_tarski(B_35)=A_36 | k1_xboole_0=A_36 | ~r1_tarski(A_36, k1_tarski(B_35)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.32  tff(c_112, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_102])).
% 2.07/1.32  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_44, c_112])).
% 2.07/1.32  tff(c_124, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.07/1.32  tff(c_4, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.32  tff(c_51, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 2.07/1.32  tff(c_165, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, k2_xboole_0(C_43, B_44)) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_171, plain, (![A_42]: (r1_tarski(A_42, k1_tarski('#skF_1')) | ~r1_tarski(A_42, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_165])).
% 2.07/1.32  tff(c_125, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.07/1.32  tff(c_16, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.32  tff(c_204, plain, (![B_54, A_55]: (k1_tarski(B_54)=A_55 | A_55='#skF_2' | ~r1_tarski(A_55, k1_tarski(B_54)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_16])).
% 2.07/1.32  tff(c_221, plain, (![A_56]: (k1_tarski('#skF_1')=A_56 | A_56='#skF_2' | ~r1_tarski(A_56, '#skF_3'))), inference(resolution, [status(thm)], [c_171, c_204])).
% 2.07/1.32  tff(c_229, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_51, c_221])).
% 2.07/1.32  tff(c_236, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_124, c_229])).
% 2.07/1.32  tff(c_126, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_2')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_4])).
% 2.07/1.32  tff(c_241, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_3')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_126])).
% 2.07/1.32  tff(c_244, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_28])).
% 2.07/1.32  tff(c_270, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_244])).
% 2.07/1.32  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_270])).
% 2.07/1.32  tff(c_272, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.07/1.32  tff(c_273, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.07/1.32  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.32  tff(c_305, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_273, c_26])).
% 2.07/1.32  tff(c_296, plain, (![A_59, B_60]: (r1_tarski(A_59, k2_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.32  tff(c_302, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_296])).
% 2.07/1.32  tff(c_274, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_28])).
% 2.07/1.32  tff(c_336, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, k2_xboole_0(C_68, B_69)) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_339, plain, (![A_67]: (r1_tarski(A_67, '#skF_2') | ~r1_tarski(A_67, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_336])).
% 2.07/1.32  tff(c_366, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.32  tff(c_377, plain, (![A_78]: (k1_tarski('#skF_1')=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_366])).
% 2.07/1.32  tff(c_383, plain, (![A_79]: (A_79='#skF_2' | k1_xboole_0=A_79 | ~r1_tarski(A_79, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_377])).
% 2.07/1.32  tff(c_404, plain, (![A_80]: (A_80='#skF_2' | k1_xboole_0=A_80 | ~r1_tarski(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_339, c_383])).
% 2.07/1.32  tff(c_412, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_302, c_404])).
% 2.07/1.32  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_305, c_412])).
% 2.07/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  
% 2.07/1.32  Inference rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Ref     : 0
% 2.07/1.32  #Sup     : 79
% 2.07/1.32  #Fact    : 0
% 2.07/1.32  #Define  : 0
% 2.07/1.32  #Split   : 3
% 2.07/1.32  #Chain   : 0
% 2.07/1.32  #Close   : 0
% 2.07/1.32  
% 2.07/1.32  Ordering : KBO
% 2.07/1.32  
% 2.07/1.32  Simplification rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Subsume      : 3
% 2.29/1.32  #Demod        : 34
% 2.29/1.32  #Tautology    : 64
% 2.29/1.32  #SimpNegUnit  : 8
% 2.29/1.32  #BackRed      : 11
% 2.29/1.32  
% 2.29/1.32  #Partial instantiations: 0
% 2.29/1.32  #Strategies tried      : 1
% 2.29/1.32  
% 2.29/1.32  Timing (in seconds)
% 2.29/1.32  ----------------------
% 2.29/1.32  Preprocessing        : 0.29
% 2.29/1.32  Parsing              : 0.15
% 2.29/1.32  CNF conversion       : 0.02
% 2.29/1.32  Main loop            : 0.21
% 2.29/1.32  Inferencing          : 0.08
% 2.29/1.32  Reduction            : 0.06
% 2.29/1.32  Demodulation         : 0.05
% 2.29/1.32  BG Simplification    : 0.01
% 2.29/1.32  Subsumption          : 0.03
% 2.29/1.32  Abstraction          : 0.01
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.53
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
