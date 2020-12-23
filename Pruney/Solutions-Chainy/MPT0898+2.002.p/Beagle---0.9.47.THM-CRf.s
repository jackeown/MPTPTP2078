%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 207 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 393 expanded)
%              Number of equality atoms :   60 ( 346 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_124,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_zfmisc_1(k3_zfmisc_1(A_33,B_34,C_35),D_36) = k4_zfmisc_1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [D_56,A_57,B_58,C_59] :
      ( k1_xboole_0 = D_56
      | k3_zfmisc_1(A_57,B_58,C_59) = k1_xboole_0
      | k4_zfmisc_1(A_57,B_58,C_59,D_56) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_310,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_295])).

tff(c_319,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_zfmisc_1(k3_zfmisc_1(A_9,B_10,C_11),D_12) = k4_zfmisc_1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_360,plain,(
    ! [B_67,D_68,A_69,C_70] :
      ( r1_tarski(B_67,D_68)
      | k2_zfmisc_1(A_69,B_67) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_69,B_67),k2_zfmisc_1(C_70,D_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_363,plain,(
    ! [C_70,C_11,B_10,D_68,D_12,A_9] :
      ( r1_tarski(D_12,D_68)
      | k2_zfmisc_1(k3_zfmisc_1(A_9,B_10,C_11),D_12) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_9,B_10,C_11,D_12),k2_zfmisc_1(C_70,D_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_360])).

tff(c_654,plain,(
    ! [A_111,B_108,C_109,D_110,C_107,D_106] :
      ( r1_tarski(D_110,D_106)
      | k4_zfmisc_1(A_111,B_108,C_109,D_110) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_111,B_108,C_109,D_110),k2_zfmisc_1(C_107,D_106)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_363])).

tff(c_678,plain,(
    ! [D_106,C_107] :
      ( r1_tarski('#skF_2',D_106)
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k2_zfmisc_1(C_107,D_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_654])).

tff(c_691,plain,(
    ! [D_106,C_107] :
      ( r1_tarski('#skF_2',D_106)
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k2_zfmisc_1(C_107,D_106)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_678])).

tff(c_693,plain,(
    ! [D_112,C_113] :
      ( r1_tarski('#skF_2',D_112)
      | ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k2_zfmisc_1(C_113,D_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_691])).

tff(c_703,plain,(
    ! [D_114,A_115,B_116,C_117] :
      ( r1_tarski('#skF_2',D_114)
      | ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k4_zfmisc_1(A_115,B_116,C_117,D_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_693])).

tff(c_731,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_703])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_733,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_731,c_2])).

tff(c_736,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_733])).

tff(c_2013,plain,(
    ! [C_233,A_235,D_234,B_232,C_229,B_231,D_230,A_236] :
      ( r1_tarski(D_230,D_234)
      | k4_zfmisc_1(A_235,B_231,C_229,D_230) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_235,B_231,C_229,D_230),k4_zfmisc_1(A_236,B_232,C_233,D_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_654])).

tff(c_2070,plain,(
    ! [D_237,A_238,B_239,C_240] :
      ( r1_tarski(D_237,'#skF_2')
      | k4_zfmisc_1(A_238,B_239,C_240,D_237) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_238,B_239,C_240,D_237),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2013])).

tff(c_2095,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2070])).

tff(c_2108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_736,c_2095])).

tff(c_2109,plain,
    ( k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_2156,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2109])).

tff(c_2110,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_130,plain,(
    ! [D_36,A_33,B_34,C_35] :
      ( k1_xboole_0 = D_36
      | k3_zfmisc_1(A_33,B_34,C_35) = k1_xboole_0
      | k4_zfmisc_1(A_33,B_34,C_35,D_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_2146,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_130])).

tff(c_2417,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_2156,c_2146])).

tff(c_2418,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2417])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( k3_zfmisc_1(A_13,B_14,C_15) != k1_xboole_0
      | k1_xboole_0 = C_15
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2477,plain,(
    ! [A_277,B_278,C_279] :
      ( k3_zfmisc_1(A_277,B_278,C_279) != '#skF_2'
      | C_279 = '#skF_2'
      | B_278 = '#skF_2'
      | A_277 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_2156,c_2156,c_2156,c_20])).

tff(c_2480,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2418,c_2477])).

tff(c_2496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_30,c_2480])).

tff(c_2498,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2109])).

tff(c_2497,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2109])).

tff(c_2502,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2497,c_20])).

tff(c_2511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2498,c_2498,c_2498,c_2502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:47:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.61  
% 3.78/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.61  %$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.78/1.61  
% 3.78/1.61  %Foreground sorts:
% 3.78/1.61  
% 3.78/1.61  
% 3.78/1.61  %Background operators:
% 3.78/1.61  
% 3.78/1.61  
% 3.78/1.61  %Foreground operators:
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.61  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.78/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.61  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.61  
% 3.78/1.62  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.78/1.62  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.78/1.62  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.78/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.78/1.62  tff(f_45, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.78/1.62  tff(f_59, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.78/1.62  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.78/1.62  tff(c_32, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.78/1.62  tff(c_124, plain, (![A_33, B_34, C_35, D_36]: (k2_zfmisc_1(k3_zfmisc_1(A_33, B_34, C_35), D_36)=k4_zfmisc_1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.62  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.62  tff(c_295, plain, (![D_56, A_57, B_58, C_59]: (k1_xboole_0=D_56 | k3_zfmisc_1(A_57, B_58, C_59)=k1_xboole_0 | k4_zfmisc_1(A_57, B_58, C_59, D_56)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 3.78/1.62  tff(c_310, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32, c_295])).
% 3.78/1.62  tff(c_319, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_310])).
% 3.78/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.62  tff(c_18, plain, (![A_9, B_10, C_11, D_12]: (k2_zfmisc_1(k3_zfmisc_1(A_9, B_10, C_11), D_12)=k4_zfmisc_1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.62  tff(c_360, plain, (![B_67, D_68, A_69, C_70]: (r1_tarski(B_67, D_68) | k2_zfmisc_1(A_69, B_67)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_69, B_67), k2_zfmisc_1(C_70, D_68)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.78/1.62  tff(c_363, plain, (![C_70, C_11, B_10, D_68, D_12, A_9]: (r1_tarski(D_12, D_68) | k2_zfmisc_1(k3_zfmisc_1(A_9, B_10, C_11), D_12)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_9, B_10, C_11, D_12), k2_zfmisc_1(C_70, D_68)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_360])).
% 3.78/1.62  tff(c_654, plain, (![A_111, B_108, C_109, D_110, C_107, D_106]: (r1_tarski(D_110, D_106) | k4_zfmisc_1(A_111, B_108, C_109, D_110)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_111, B_108, C_109, D_110), k2_zfmisc_1(C_107, D_106)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_363])).
% 3.78/1.62  tff(c_678, plain, (![D_106, C_107]: (r1_tarski('#skF_2', D_106) | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k2_zfmisc_1(C_107, D_106)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_654])).
% 3.78/1.62  tff(c_691, plain, (![D_106, C_107]: (r1_tarski('#skF_2', D_106) | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k2_zfmisc_1(C_107, D_106)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_678])).
% 3.78/1.62  tff(c_693, plain, (![D_112, C_113]: (r1_tarski('#skF_2', D_112) | ~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k2_zfmisc_1(C_113, D_112)))), inference(negUnitSimplification, [status(thm)], [c_319, c_691])).
% 3.78/1.62  tff(c_703, plain, (![D_114, A_115, B_116, C_117]: (r1_tarski('#skF_2', D_114) | ~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k4_zfmisc_1(A_115, B_116, C_117, D_114)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_693])).
% 3.78/1.62  tff(c_731, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_6, c_703])).
% 3.78/1.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.62  tff(c_733, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_731, c_2])).
% 3.78/1.62  tff(c_736, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_733])).
% 3.78/1.62  tff(c_2013, plain, (![C_233, A_235, D_234, B_232, C_229, B_231, D_230, A_236]: (r1_tarski(D_230, D_234) | k4_zfmisc_1(A_235, B_231, C_229, D_230)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_235, B_231, C_229, D_230), k4_zfmisc_1(A_236, B_232, C_233, D_234)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_654])).
% 3.78/1.62  tff(c_2070, plain, (![D_237, A_238, B_239, C_240]: (r1_tarski(D_237, '#skF_2') | k4_zfmisc_1(A_238, B_239, C_240, D_237)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_238, B_239, C_240, D_237), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2013])).
% 3.78/1.62  tff(c_2095, plain, (r1_tarski('#skF_1', '#skF_2') | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2070])).
% 3.78/1.62  tff(c_2108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_736, c_2095])).
% 3.78/1.62  tff(c_2109, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_310])).
% 3.78/1.62  tff(c_2156, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2109])).
% 3.78/1.62  tff(c_2110, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_310])).
% 3.78/1.62  tff(c_130, plain, (![D_36, A_33, B_34, C_35]: (k1_xboole_0=D_36 | k3_zfmisc_1(A_33, B_34, C_35)=k1_xboole_0 | k4_zfmisc_1(A_33, B_34, C_35, D_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 3.78/1.62  tff(c_2146, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2110, c_130])).
% 3.78/1.62  tff(c_2417, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_2156, c_2146])).
% 3.78/1.62  tff(c_2418, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_30, c_2417])).
% 3.78/1.62  tff(c_20, plain, (![A_13, B_14, C_15]: (k3_zfmisc_1(A_13, B_14, C_15)!=k1_xboole_0 | k1_xboole_0=C_15 | k1_xboole_0=B_14 | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.78/1.62  tff(c_2477, plain, (![A_277, B_278, C_279]: (k3_zfmisc_1(A_277, B_278, C_279)!='#skF_2' | C_279='#skF_2' | B_278='#skF_2' | A_277='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_2156, c_2156, c_2156, c_20])).
% 3.78/1.62  tff(c_2480, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2418, c_2477])).
% 3.78/1.62  tff(c_2496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_30, c_2480])).
% 3.78/1.62  tff(c_2498, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2109])).
% 3.78/1.62  tff(c_2497, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2109])).
% 3.78/1.62  tff(c_2502, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2497, c_20])).
% 3.78/1.62  tff(c_2511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2498, c_2498, c_2498, c_2502])).
% 3.78/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.62  
% 3.78/1.62  Inference rules
% 3.78/1.62  ----------------------
% 3.78/1.62  #Ref     : 0
% 3.78/1.62  #Sup     : 598
% 3.78/1.62  #Fact    : 0
% 3.78/1.62  #Define  : 0
% 3.78/1.62  #Split   : 7
% 3.78/1.62  #Chain   : 0
% 3.78/1.62  #Close   : 0
% 3.78/1.62  
% 3.78/1.62  Ordering : KBO
% 3.78/1.62  
% 3.78/1.62  Simplification rules
% 3.78/1.62  ----------------------
% 3.78/1.62  #Subsume      : 72
% 3.78/1.62  #Demod        : 565
% 3.78/1.62  #Tautology    : 385
% 3.78/1.62  #SimpNegUnit  : 11
% 3.78/1.62  #BackRed      : 104
% 3.78/1.62  
% 3.78/1.62  #Partial instantiations: 0
% 3.78/1.62  #Strategies tried      : 1
% 3.78/1.62  
% 3.78/1.62  Timing (in seconds)
% 3.78/1.63  ----------------------
% 3.78/1.63  Preprocessing        : 0.29
% 3.78/1.63  Parsing              : 0.15
% 3.78/1.63  CNF conversion       : 0.02
% 3.78/1.63  Main loop            : 0.59
% 3.78/1.63  Inferencing          : 0.20
% 3.78/1.63  Reduction            : 0.20
% 3.78/1.63  Demodulation         : 0.15
% 3.78/1.63  BG Simplification    : 0.02
% 3.78/1.63  Subsumption          : 0.12
% 3.78/1.63  Abstraction          : 0.03
% 3.78/1.63  MUC search           : 0.00
% 3.78/1.63  Cooper               : 0.00
% 3.78/1.63  Total                : 0.90
% 3.78/1.63  Index Insertion      : 0.00
% 3.78/1.63  Index Deletion       : 0.00
% 3.78/1.63  Index Matching       : 0.00
% 3.78/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
