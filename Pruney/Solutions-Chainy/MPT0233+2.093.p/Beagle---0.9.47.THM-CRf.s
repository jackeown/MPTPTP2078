%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:33 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 129 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 150 expanded)
%              Number of equality atoms :   50 (  96 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_70,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [D_25,B_21] : r2_hidden(D_25,k2_tarski(D_25,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_181,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [A_79] : k3_xboole_0(k1_xboole_0,A_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [A_79] : k3_xboole_0(A_79,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_24,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_352,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_364,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_352])).

tff(c_379,plain,(
    ! [A_79] : k4_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_364])).

tff(c_464,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_483,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k3_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_464])).

tff(c_494,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_483])).

tff(c_1922,plain,(
    ! [A_151,C_152,B_153] :
      ( ~ r2_hidden(A_151,C_152)
      | k4_xboole_0(k2_tarski(A_151,B_153),C_152) != k1_tarski(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1933,plain,(
    ! [A_151,B_153] :
      ( ~ r2_hidden(A_151,k2_tarski(A_151,B_153))
      | k1_tarski(A_151) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_1922])).

tff(c_1946,plain,(
    ! [A_151] : k1_tarski(A_151) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1933])).

tff(c_427,plain,(
    ! [A_89,B_90] : k3_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) = k1_tarski(A_89) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_119,plain,(
    ! [B_71,A_72] : k3_xboole_0(B_71,A_72) = k3_xboole_0(A_72,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [B_71,A_72] : r1_tarski(k3_xboole_0(B_71,A_72),A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_14])).

tff(c_436,plain,(
    ! [A_89,B_90] : r1_tarski(k1_tarski(A_89),k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_134])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_859,plain,(
    ! [A_109,C_110,B_111] :
      ( r1_tarski(A_109,C_110)
      | ~ r1_tarski(B_111,C_110)
      | ~ r1_tarski(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1024,plain,(
    ! [A_120] :
      ( r1_tarski(A_120,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_120,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_72,c_859])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1949,plain,(
    ! [A_155] :
      ( k3_xboole_0(A_155,k2_tarski('#skF_5','#skF_6')) = A_155
      | ~ r1_tarski(A_155,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1024,c_18])).

tff(c_1990,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_1949])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_640,plain,(
    ! [A_101,B_102] : k3_xboole_0(k3_xboole_0(A_101,B_102),A_101) = k3_xboole_0(A_101,B_102) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_370,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_352])).

tff(c_649,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,k3_xboole_0(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_370])).

tff(c_710,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_649])).

tff(c_2541,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_710])).

tff(c_2589,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_2541])).

tff(c_44,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    ! [B_55,C_56] :
      ( k4_xboole_0(k2_tarski(B_55,B_55),C_56) = k1_tarski(B_55)
      | r2_hidden(B_55,C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73,plain,(
    ! [B_55,C_56] :
      ( k4_xboole_0(k1_tarski(B_55),C_56) = k1_tarski(B_55)
      | r2_hidden(B_55,C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62])).

tff(c_2602,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2589,c_73])).

tff(c_2611,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1946,c_2602])).

tff(c_26,plain,(
    ! [D_25,B_21,A_20] :
      ( D_25 = B_21
      | D_25 = A_20
      | ~ r2_hidden(D_25,k2_tarski(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2617,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2611,c_26])).

tff(c_2621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_68,c_2617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:53:44 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.44/1.61  
% 3.44/1.61  %Foreground sorts:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Background operators:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Foreground operators:
% 3.44/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  
% 3.44/1.62  tff(f_99, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.44/1.62  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.44/1.62  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.62  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.44/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.62  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.44/1.62  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.62  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.44/1.62  tff(f_87, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.44/1.62  tff(f_89, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.44/1.62  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.44/1.62  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.44/1.62  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.62  tff(c_70, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.44/1.62  tff(c_68, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.44/1.62  tff(c_30, plain, (![D_25, B_21]: (r2_hidden(D_25, k2_tarski(D_25, B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.62  tff(c_20, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.62  tff(c_181, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.62  tff(c_203, plain, (![A_79]: (k3_xboole_0(k1_xboole_0, A_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_181])).
% 3.44/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.62  tff(c_211, plain, (![A_79]: (k3_xboole_0(A_79, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 3.44/1.62  tff(c_24, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.62  tff(c_352, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.62  tff(c_364, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=k4_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_352])).
% 3.44/1.62  tff(c_379, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_364])).
% 3.44/1.62  tff(c_464, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.62  tff(c_483, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k3_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_379, c_464])).
% 3.44/1.62  tff(c_494, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_483])).
% 3.44/1.62  tff(c_1922, plain, (![A_151, C_152, B_153]: (~r2_hidden(A_151, C_152) | k4_xboole_0(k2_tarski(A_151, B_153), C_152)!=k1_tarski(A_151))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.62  tff(c_1933, plain, (![A_151, B_153]: (~r2_hidden(A_151, k2_tarski(A_151, B_153)) | k1_tarski(A_151)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_494, c_1922])).
% 3.44/1.62  tff(c_1946, plain, (![A_151]: (k1_tarski(A_151)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1933])).
% 3.44/1.62  tff(c_427, plain, (![A_89, B_90]: (k3_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90))=k1_tarski(A_89))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.44/1.62  tff(c_119, plain, (![B_71, A_72]: (k3_xboole_0(B_71, A_72)=k3_xboole_0(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.62  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.62  tff(c_134, plain, (![B_71, A_72]: (r1_tarski(k3_xboole_0(B_71, A_72), A_72))), inference(superposition, [status(thm), theory('equality')], [c_119, c_14])).
% 3.44/1.62  tff(c_436, plain, (![A_89, B_90]: (r1_tarski(k1_tarski(A_89), k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_427, c_134])).
% 3.44/1.62  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.44/1.62  tff(c_859, plain, (![A_109, C_110, B_111]: (r1_tarski(A_109, C_110) | ~r1_tarski(B_111, C_110) | ~r1_tarski(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.62  tff(c_1024, plain, (![A_120]: (r1_tarski(A_120, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_120, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_72, c_859])).
% 3.44/1.62  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.62  tff(c_1949, plain, (![A_155]: (k3_xboole_0(A_155, k2_tarski('#skF_5', '#skF_6'))=A_155 | ~r1_tarski(A_155, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_1024, c_18])).
% 3.44/1.62  tff(c_1990, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_436, c_1949])).
% 3.44/1.62  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.62  tff(c_640, plain, (![A_101, B_102]: (k3_xboole_0(k3_xboole_0(A_101, B_102), A_101)=k3_xboole_0(A_101, B_102))), inference(resolution, [status(thm)], [c_14, c_181])).
% 3.44/1.62  tff(c_370, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_352])).
% 3.44/1.62  tff(c_649, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, k3_xboole_0(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_640, c_370])).
% 3.44/1.62  tff(c_710, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_649])).
% 3.44/1.62  tff(c_2541, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1990, c_710])).
% 3.44/1.62  tff(c_2589, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_494, c_2541])).
% 3.44/1.62  tff(c_44, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.62  tff(c_62, plain, (![B_55, C_56]: (k4_xboole_0(k2_tarski(B_55, B_55), C_56)=k1_tarski(B_55) | r2_hidden(B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.62  tff(c_73, plain, (![B_55, C_56]: (k4_xboole_0(k1_tarski(B_55), C_56)=k1_tarski(B_55) | r2_hidden(B_55, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62])).
% 3.44/1.62  tff(c_2602, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2589, c_73])).
% 3.44/1.62  tff(c_2611, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1946, c_2602])).
% 3.44/1.62  tff(c_26, plain, (![D_25, B_21, A_20]: (D_25=B_21 | D_25=A_20 | ~r2_hidden(D_25, k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.62  tff(c_2617, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2611, c_26])).
% 3.44/1.62  tff(c_2621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_68, c_2617])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 618
% 3.44/1.62  #Fact    : 0
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 1
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 24
% 3.44/1.62  #Demod        : 486
% 3.44/1.62  #Tautology    : 438
% 3.44/1.62  #SimpNegUnit  : 3
% 3.44/1.62  #BackRed      : 1
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 0
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.33
% 3.44/1.62  Parsing              : 0.17
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.53
% 3.44/1.62  Inferencing          : 0.16
% 3.44/1.62  Reduction            : 0.23
% 3.44/1.62  Demodulation         : 0.19
% 3.44/1.62  BG Simplification    : 0.03
% 3.82/1.62  Subsumption          : 0.09
% 3.82/1.62  Abstraction          : 0.03
% 3.82/1.63  MUC search           : 0.00
% 3.82/1.63  Cooper               : 0.00
% 3.82/1.63  Total                : 0.90
% 3.82/1.63  Index Insertion      : 0.00
% 3.82/1.63  Index Deletion       : 0.00
% 3.82/1.63  Index Matching       : 0.00
% 3.82/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
