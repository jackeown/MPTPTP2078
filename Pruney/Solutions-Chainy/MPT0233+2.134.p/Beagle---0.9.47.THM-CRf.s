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
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   77 (  86 expanded)
%              Number of leaves         :   41 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 (  84 expanded)
%              Number of equality atoms :   50 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_86,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_797,plain,(
    ! [A_152,B_153,C_154,D_155] : k2_xboole_0(k1_enumset1(A_152,B_153,C_154),k1_tarski(D_155)) = k2_enumset1(A_152,B_153,C_154,D_155) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_821,plain,(
    ! [A_41,B_42,D_155] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_155)) = k2_enumset1(A_41,A_41,B_42,D_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_797])).

tff(c_824,plain,(
    ! [A_41,B_42,D_155] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_155)) = k1_enumset1(A_41,B_42,D_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_821])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_340,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_355,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_359,plain,(
    ! [A_109] : k4_xboole_0(A_109,k1_xboole_0) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_355])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_368,plain,(
    ! [A_109] : k4_xboole_0(A_109,A_109) = k3_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_12])).

tff(c_373,plain,(
    ! [A_109] : k4_xboole_0(A_109,A_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_368])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_352,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_340])).

tff(c_413,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_352])).

tff(c_82,plain,(
    ! [A_71,B_72] : r1_tarski(k1_tarski(A_71),k2_tarski(A_71,B_72)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_88,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_580,plain,(
    ! [A_127,C_128,B_129] :
      ( r1_tarski(A_127,C_128)
      | ~ r1_tarski(B_129,C_128)
      | ~ r1_tarski(A_127,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_736,plain,(
    ! [A_145] :
      ( r1_tarski(A_145,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_145,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_88,c_580])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_925,plain,(
    ! [A_163] :
      ( k3_xboole_0(A_163,k2_tarski('#skF_7','#skF_8')) = A_163
      | ~ r1_tarski(A_163,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_736,c_8])).

tff(c_935,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_925])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_942,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_4])).

tff(c_946,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_942])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_951,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_16])).

tff(c_957,plain,(
    k1_enumset1('#skF_7','#skF_8','#skF_5') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_14,c_951])).

tff(c_20,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_972,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_20])).

tff(c_42,plain,(
    ! [D_28,B_24,A_23] :
      ( D_28 = B_24
      | D_28 = A_23
      | ~ r2_hidden(D_28,k2_tarski(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_981,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_972,c_42])).

tff(c_985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.04/1.47  
% 3.04/1.47  %Foreground sorts:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Background operators:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Foreground operators:
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.04/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.04/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.04/1.47  
% 3.04/1.48  tff(f_105, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.04/1.48  tff(f_83, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.04/1.48  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.04/1.48  tff(f_77, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.04/1.48  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.04/1.48  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.04/1.48  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.04/1.48  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.04/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.04/1.48  tff(f_95, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.04/1.48  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.04/1.48  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.48  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.04/1.48  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.04/1.48  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.04/1.48  tff(c_86, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.04/1.48  tff(c_84, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.04/1.48  tff(c_70, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.04/1.48  tff(c_68, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.48  tff(c_797, plain, (![A_152, B_153, C_154, D_155]: (k2_xboole_0(k1_enumset1(A_152, B_153, C_154), k1_tarski(D_155))=k2_enumset1(A_152, B_153, C_154, D_155))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.48  tff(c_821, plain, (![A_41, B_42, D_155]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_155))=k2_enumset1(A_41, A_41, B_42, D_155))), inference(superposition, [status(thm), theory('equality')], [c_68, c_797])).
% 3.04/1.48  tff(c_824, plain, (![A_41, B_42, D_155]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_155))=k1_enumset1(A_41, B_42, D_155))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_821])).
% 3.04/1.48  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.48  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.48  tff(c_340, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.04/1.48  tff(c_355, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_340])).
% 3.04/1.48  tff(c_359, plain, (![A_109]: (k4_xboole_0(A_109, k1_xboole_0)=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_355])).
% 3.04/1.48  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.48  tff(c_368, plain, (![A_109]: (k4_xboole_0(A_109, A_109)=k3_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_359, c_12])).
% 3.04/1.48  tff(c_373, plain, (![A_109]: (k4_xboole_0(A_109, A_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_368])).
% 3.04/1.48  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.04/1.48  tff(c_352, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_340])).
% 3.04/1.48  tff(c_413, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_373, c_352])).
% 3.04/1.48  tff(c_82, plain, (![A_71, B_72]: (r1_tarski(k1_tarski(A_71), k2_tarski(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.04/1.48  tff(c_88, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.04/1.48  tff(c_580, plain, (![A_127, C_128, B_129]: (r1_tarski(A_127, C_128) | ~r1_tarski(B_129, C_128) | ~r1_tarski(A_127, B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.48  tff(c_736, plain, (![A_145]: (r1_tarski(A_145, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_145, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_88, c_580])).
% 3.04/1.48  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.48  tff(c_925, plain, (![A_163]: (k3_xboole_0(A_163, k2_tarski('#skF_7', '#skF_8'))=A_163 | ~r1_tarski(A_163, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_736, c_8])).
% 3.04/1.48  tff(c_935, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_925])).
% 3.04/1.48  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.04/1.48  tff(c_942, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_935, c_4])).
% 3.04/1.48  tff(c_946, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_413, c_942])).
% 3.04/1.48  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.48  tff(c_951, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_946, c_16])).
% 3.04/1.48  tff(c_957, plain, (k1_enumset1('#skF_7', '#skF_8', '#skF_5')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_14, c_951])).
% 3.04/1.48  tff(c_20, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.48  tff(c_972, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_957, c_20])).
% 3.04/1.48  tff(c_42, plain, (![D_28, B_24, A_23]: (D_28=B_24 | D_28=A_23 | ~r2_hidden(D_28, k2_tarski(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.48  tff(c_981, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_972, c_42])).
% 3.04/1.48  tff(c_985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_981])).
% 3.04/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  Inference rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Ref     : 0
% 3.04/1.48  #Sup     : 215
% 3.04/1.48  #Fact    : 0
% 3.04/1.48  #Define  : 0
% 3.04/1.48  #Split   : 0
% 3.04/1.48  #Chain   : 0
% 3.04/1.48  #Close   : 0
% 3.04/1.48  
% 3.04/1.48  Ordering : KBO
% 3.04/1.48  
% 3.04/1.48  Simplification rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Subsume      : 2
% 3.04/1.48  #Demod        : 124
% 3.04/1.48  #Tautology    : 169
% 3.04/1.48  #SimpNegUnit  : 1
% 3.04/1.48  #BackRed      : 4
% 3.04/1.48  
% 3.04/1.48  #Partial instantiations: 0
% 3.04/1.48  #Strategies tried      : 1
% 3.04/1.48  
% 3.04/1.48  Timing (in seconds)
% 3.04/1.48  ----------------------
% 3.26/1.49  Preprocessing        : 0.36
% 3.26/1.49  Parsing              : 0.18
% 3.26/1.49  CNF conversion       : 0.03
% 3.26/1.49  Main loop            : 0.35
% 3.26/1.49  Inferencing          : 0.12
% 3.26/1.49  Reduction            : 0.13
% 3.26/1.49  Demodulation         : 0.10
% 3.26/1.49  BG Simplification    : 0.02
% 3.26/1.49  Subsumption          : 0.06
% 3.26/1.49  Abstraction          : 0.02
% 3.26/1.49  MUC search           : 0.00
% 3.26/1.49  Cooper               : 0.00
% 3.26/1.49  Total                : 0.75
% 3.26/1.49  Index Insertion      : 0.00
% 3.26/1.49  Index Deletion       : 0.00
% 3.26/1.49  Index Matching       : 0.00
% 3.26/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
