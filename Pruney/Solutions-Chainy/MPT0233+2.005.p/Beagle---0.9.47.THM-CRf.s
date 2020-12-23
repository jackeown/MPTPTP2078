%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   86 (  96 expanded)
%              Number of leaves         :   43 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 (  99 expanded)
%              Number of equality atoms :   62 (  74 expanded)
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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_77,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_92,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_90,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1137,plain,(
    ! [A_167,B_168,C_169,D_170] : k2_xboole_0(k2_tarski(A_167,B_168),k2_tarski(C_169,D_170)) = k2_enumset1(A_167,B_168,C_169,D_170) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1166,plain,(
    ! [A_37,C_169,D_170] : k2_xboole_0(k1_tarski(A_37),k2_tarski(C_169,D_170)) = k2_enumset1(A_37,A_37,C_169,D_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1137])).

tff(c_1436,plain,(
    ! [A_188,C_189,D_190] : k2_xboole_0(k1_tarski(A_188),k2_tarski(C_189,D_190)) = k1_enumset1(A_188,C_189,D_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1166])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_364,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_385,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_364])).

tff(c_389,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_385])).

tff(c_591,plain,(
    ! [A_120,B_121] : k4_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_623,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_591])).

tff(c_631,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_623])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_364])).

tff(c_633,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_382])).

tff(c_86,plain,(
    ! [B_66,C_67] : r1_tarski(k1_tarski(B_66),k2_tarski(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_94,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_292,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0(A_99,B_100) = A_99
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_292])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_491,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_tarski(A_113,B_114)
      | ~ r1_tarski(A_113,k3_xboole_0(B_114,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_919,plain,(
    ! [A_143,A_144,B_145] :
      ( r1_tarski(A_143,A_144)
      | ~ r1_tarski(A_143,k3_xboole_0(B_145,A_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_491])).

tff(c_952,plain,(
    ! [A_149] :
      ( r1_tarski(A_149,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_149,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_919])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1223,plain,(
    ! [A_174] :
      ( k3_xboole_0(A_174,k2_tarski('#skF_7','#skF_8')) = A_174
      | ~ r1_tarski(A_174,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_952,c_12])).

tff(c_1252,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1223])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1272,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_8])).

tff(c_1276,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_1272])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1284,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_20])).

tff(c_1288,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1284])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1387,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_2])).

tff(c_1442,plain,(
    k1_enumset1('#skF_5','#skF_7','#skF_8') = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_1387])).

tff(c_28,plain,(
    ! [E_26,B_21,C_22] : r2_hidden(E_26,k1_enumset1(E_26,B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1538,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_28])).

tff(c_46,plain,(
    ! [D_32,B_28,A_27] :
      ( D_32 = B_28
      | D_32 = A_27
      | ~ r2_hidden(D_32,k2_tarski(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1561,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1538,c_46])).

tff(c_1565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_1561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.65  
% 3.38/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.66  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.38/1.66  
% 3.38/1.66  %Foreground sorts:
% 3.38/1.66  
% 3.38/1.66  
% 3.38/1.66  %Background operators:
% 3.38/1.66  
% 3.38/1.66  
% 3.38/1.66  %Foreground operators:
% 3.38/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.38/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.38/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.38/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.38/1.66  
% 3.38/1.67  tff(f_114, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.38/1.67  tff(f_81, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.38/1.67  tff(f_77, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.67  tff(f_75, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.38/1.67  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.67  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.38/1.67  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.67  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.38/1.67  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.38/1.67  tff(f_104, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.38/1.67  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.67  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.38/1.67  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.38/1.67  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.38/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.38/1.67  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.38/1.67  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.38/1.67  tff(c_92, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.38/1.67  tff(c_90, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.38/1.67  tff(c_70, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.67  tff(c_66, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.67  tff(c_1137, plain, (![A_167, B_168, C_169, D_170]: (k2_xboole_0(k2_tarski(A_167, B_168), k2_tarski(C_169, D_170))=k2_enumset1(A_167, B_168, C_169, D_170))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.38/1.67  tff(c_1166, plain, (![A_37, C_169, D_170]: (k2_xboole_0(k1_tarski(A_37), k2_tarski(C_169, D_170))=k2_enumset1(A_37, A_37, C_169, D_170))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1137])).
% 3.38/1.67  tff(c_1436, plain, (![A_188, C_189, D_190]: (k2_xboole_0(k1_tarski(A_188), k2_tarski(C_189, D_190))=k1_enumset1(A_188, C_189, D_190))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1166])).
% 3.38/1.67  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.67  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.67  tff(c_364, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.67  tff(c_385, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_364])).
% 3.38/1.67  tff(c_389, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_385])).
% 3.38/1.67  tff(c_591, plain, (![A_120, B_121]: (k4_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.67  tff(c_623, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_389, c_591])).
% 3.38/1.67  tff(c_631, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_623])).
% 3.38/1.67  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.67  tff(c_382, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_364])).
% 3.38/1.67  tff(c_633, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_631, c_382])).
% 3.38/1.67  tff(c_86, plain, (![B_66, C_67]: (r1_tarski(k1_tarski(B_66), k2_tarski(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.67  tff(c_94, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.38/1.67  tff(c_292, plain, (![A_99, B_100]: (k3_xboole_0(A_99, B_100)=A_99 | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.67  tff(c_315, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_292])).
% 3.38/1.67  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.67  tff(c_491, plain, (![A_113, B_114, C_115]: (r1_tarski(A_113, B_114) | ~r1_tarski(A_113, k3_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.67  tff(c_919, plain, (![A_143, A_144, B_145]: (r1_tarski(A_143, A_144) | ~r1_tarski(A_143, k3_xboole_0(B_145, A_144)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_491])).
% 3.38/1.67  tff(c_952, plain, (![A_149]: (r1_tarski(A_149, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_149, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_315, c_919])).
% 3.38/1.67  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.67  tff(c_1223, plain, (![A_174]: (k3_xboole_0(A_174, k2_tarski('#skF_7', '#skF_8'))=A_174 | ~r1_tarski(A_174, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_952, c_12])).
% 3.38/1.67  tff(c_1252, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_86, c_1223])).
% 3.38/1.67  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.67  tff(c_1272, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_8])).
% 3.38/1.67  tff(c_1276, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_633, c_1272])).
% 3.38/1.67  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.67  tff(c_1284, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1276, c_20])).
% 3.38/1.67  tff(c_1288, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1284])).
% 3.38/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.67  tff(c_1387, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1288, c_2])).
% 3.38/1.67  tff(c_1442, plain, (k1_enumset1('#skF_5', '#skF_7', '#skF_8')=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1436, c_1387])).
% 3.38/1.67  tff(c_28, plain, (![E_26, B_21, C_22]: (r2_hidden(E_26, k1_enumset1(E_26, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.67  tff(c_1538, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_28])).
% 3.38/1.67  tff(c_46, plain, (![D_32, B_28, A_27]: (D_32=B_28 | D_32=A_27 | ~r2_hidden(D_32, k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.67  tff(c_1561, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1538, c_46])).
% 3.38/1.67  tff(c_1565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_1561])).
% 3.38/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.67  
% 3.38/1.67  Inference rules
% 3.38/1.67  ----------------------
% 3.38/1.67  #Ref     : 0
% 3.38/1.67  #Sup     : 361
% 3.38/1.67  #Fact    : 0
% 3.38/1.67  #Define  : 0
% 3.38/1.67  #Split   : 0
% 3.38/1.67  #Chain   : 0
% 3.38/1.67  #Close   : 0
% 3.38/1.67  
% 3.38/1.67  Ordering : KBO
% 3.38/1.67  
% 3.38/1.67  Simplification rules
% 3.38/1.67  ----------------------
% 3.38/1.67  #Subsume      : 9
% 3.38/1.67  #Demod        : 180
% 3.38/1.67  #Tautology    : 271
% 3.38/1.67  #SimpNegUnit  : 1
% 3.38/1.67  #BackRed      : 2
% 3.38/1.67  
% 3.38/1.67  #Partial instantiations: 0
% 3.38/1.67  #Strategies tried      : 1
% 3.38/1.67  
% 3.38/1.67  Timing (in seconds)
% 3.38/1.67  ----------------------
% 3.38/1.68  Preprocessing        : 0.38
% 3.38/1.68  Parsing              : 0.19
% 3.38/1.68  CNF conversion       : 0.03
% 3.38/1.68  Main loop            : 0.49
% 3.38/1.68  Inferencing          : 0.17
% 3.38/1.68  Reduction            : 0.19
% 3.38/1.68  Demodulation         : 0.14
% 3.38/1.68  BG Simplification    : 0.03
% 3.38/1.68  Subsumption          : 0.08
% 3.38/1.68  Abstraction          : 0.02
% 3.38/1.68  MUC search           : 0.00
% 3.38/1.68  Cooper               : 0.00
% 3.38/1.68  Total                : 0.91
% 3.38/1.68  Index Insertion      : 0.00
% 3.38/1.68  Index Deletion       : 0.00
% 3.38/1.68  Index Matching       : 0.00
% 3.38/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
