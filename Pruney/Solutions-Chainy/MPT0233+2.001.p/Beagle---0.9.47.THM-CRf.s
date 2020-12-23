%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 135 expanded)
%              Number of leaves         :   44 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 169 expanded)
%              Number of equality atoms :   52 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_132,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_109,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_106,plain,(
    '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_104,plain,(
    '#skF_7' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,(
    ! [D_43,B_39] : r2_hidden(D_43,k2_tarski(D_43,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_391,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_xboole_0(A_120,B_121)
      | ~ r2_hidden(C_122,k3_xboole_0(A_120,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,(
    ! [A_126,B_127] :
      ( ~ r1_xboole_0(A_126,B_127)
      | k3_xboole_0(A_126,B_127) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_391])).

tff(c_425,plain,(
    ! [A_28] : k3_xboole_0(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_421])).

tff(c_30,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_426,plain,(
    ! [A_128] : k3_xboole_0(A_128,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_421])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_434,plain,(
    ! [A_128] : k5_xboole_0(A_128,k1_xboole_0) = k4_xboole_0(A_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_20])).

tff(c_585,plain,(
    ! [A_133] : k4_xboole_0(A_133,k1_xboole_0) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_434])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_591,plain,(
    ! [A_133] : k4_xboole_0(A_133,A_133) = k3_xboole_0(A_133,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_28])).

tff(c_599,plain,(
    ! [A_133] : k4_xboole_0(A_133,A_133) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_591])).

tff(c_2662,plain,(
    ! [A_211,C_212,B_213] :
      ( ~ r2_hidden(A_211,C_212)
      | k4_xboole_0(k2_tarski(A_211,B_213),C_212) != k1_tarski(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2669,plain,(
    ! [A_211,B_213] :
      ( ~ r2_hidden(A_211,k2_tarski(A_211,B_213))
      | k1_tarski(A_211) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_2662])).

tff(c_2682,plain,(
    ! [A_211] : k1_tarski(A_211) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2669])).

tff(c_473,plain,(
    ! [A_129,B_130] : k3_xboole_0(k1_tarski(A_129),k2_tarski(A_129,B_130)) = k1_tarski(A_129) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_189,plain,(
    ! [B_96,A_97] : k3_xboole_0(B_96,A_97) = k3_xboole_0(A_97,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_204,plain,(
    ! [B_96,A_97] : r1_tarski(k3_xboole_0(B_96,A_97),A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_485,plain,(
    ! [A_129,B_130] : r1_tarski(k1_tarski(A_129),k2_tarski(A_129,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_204])).

tff(c_108,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1952,plain,(
    ! [A_184,C_185,B_186] :
      ( r1_tarski(A_184,C_185)
      | ~ r1_tarski(B_186,C_185)
      | ~ r1_tarski(A_184,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2164,plain,(
    ! [A_195] :
      ( r1_tarski(A_195,k2_tarski('#skF_9','#skF_10'))
      | ~ r1_tarski(A_195,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_108,c_1952])).

tff(c_2190,plain,(
    r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_485,c_2164])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2206,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_2190,c_26])).

tff(c_245,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = A_109
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1040,plain,(
    ! [A_162,B_163] : k3_xboole_0(k3_xboole_0(A_162,B_163),A_162) = k3_xboole_0(A_162,B_163) ),
    inference(resolution,[status(thm)],[c_22,c_245])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_284,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_296,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_284])).

tff(c_1052,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k3_xboole_0(A_162,B_163)) = k4_xboole_0(A_162,k3_xboole_0(A_162,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_296])).

tff(c_1119,plain,(
    ! [A_162,B_163] : k4_xboole_0(A_162,k3_xboole_0(A_162,B_163)) = k4_xboole_0(A_162,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1052])).

tff(c_3858,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2206,c_1119])).

tff(c_3934,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_3858])).

tff(c_80,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_98,plain,(
    ! [B_77,C_78] :
      ( k4_xboole_0(k2_tarski(B_77,B_77),C_78) = k1_tarski(B_77)
      | r2_hidden(B_77,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_109,plain,(
    ! [B_77,C_78] :
      ( k4_xboole_0(k1_tarski(B_77),C_78) = k1_tarski(B_77)
      | r2_hidden(B_77,C_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98])).

tff(c_3952,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | r2_hidden('#skF_7',k2_tarski('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3934,c_109])).

tff(c_3964,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_2682,c_3952])).

tff(c_60,plain,(
    ! [D_43,B_39,A_38] :
      ( D_43 = B_39
      | D_43 = A_38
      | ~ r2_hidden(D_43,k2_tarski(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3971,plain,
    ( '#skF_7' = '#skF_10'
    | '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3964,c_60])).

tff(c_3975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_104,c_3971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.85  
% 4.62/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 4.62/1.85  
% 4.62/1.85  %Foreground sorts:
% 4.62/1.85  
% 4.62/1.85  
% 4.62/1.85  %Background operators:
% 4.62/1.85  
% 4.62/1.85  
% 4.62/1.85  %Foreground operators:
% 4.62/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.62/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_10', type, '#skF_10': $i).
% 4.62/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.62/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.62/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_9', type, '#skF_9': $i).
% 4.62/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.62/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.62/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.85  
% 4.62/1.86  tff(f_142, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.62/1.86  tff(f_105, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.62/1.86  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.62/1.86  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.62/1.86  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.62/1.86  tff(f_77, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.62/1.86  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.62/1.86  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.62/1.86  tff(f_130, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 4.62/1.86  tff(f_132, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 4.62/1.86  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.62/1.86  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.62/1.86  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.62/1.86  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.62/1.86  tff(f_109, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.62/1.86  tff(c_106, plain, ('#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.86  tff(c_104, plain, ('#skF_7'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.86  tff(c_64, plain, (![D_43, B_39]: (r2_hidden(D_43, k2_tarski(D_43, B_39)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.86  tff(c_32, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.62/1.86  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.86  tff(c_391, plain, (![A_120, B_121, C_122]: (~r1_xboole_0(A_120, B_121) | ~r2_hidden(C_122, k3_xboole_0(A_120, B_121)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.86  tff(c_421, plain, (![A_126, B_127]: (~r1_xboole_0(A_126, B_127) | k3_xboole_0(A_126, B_127)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_391])).
% 4.62/1.86  tff(c_425, plain, (![A_28]: (k3_xboole_0(A_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_421])).
% 4.62/1.86  tff(c_30, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.62/1.86  tff(c_426, plain, (![A_128]: (k3_xboole_0(A_128, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_421])).
% 4.62/1.86  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.86  tff(c_434, plain, (![A_128]: (k5_xboole_0(A_128, k1_xboole_0)=k4_xboole_0(A_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_426, c_20])).
% 4.62/1.86  tff(c_585, plain, (![A_133]: (k4_xboole_0(A_133, k1_xboole_0)=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_434])).
% 4.62/1.86  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.62/1.86  tff(c_591, plain, (![A_133]: (k4_xboole_0(A_133, A_133)=k3_xboole_0(A_133, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_585, c_28])).
% 4.62/1.86  tff(c_599, plain, (![A_133]: (k4_xboole_0(A_133, A_133)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_591])).
% 4.62/1.86  tff(c_2662, plain, (![A_211, C_212, B_213]: (~r2_hidden(A_211, C_212) | k4_xboole_0(k2_tarski(A_211, B_213), C_212)!=k1_tarski(A_211))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.62/1.86  tff(c_2669, plain, (![A_211, B_213]: (~r2_hidden(A_211, k2_tarski(A_211, B_213)) | k1_tarski(A_211)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_599, c_2662])).
% 4.62/1.86  tff(c_2682, plain, (![A_211]: (k1_tarski(A_211)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2669])).
% 4.62/1.86  tff(c_473, plain, (![A_129, B_130]: (k3_xboole_0(k1_tarski(A_129), k2_tarski(A_129, B_130))=k1_tarski(A_129))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.62/1.86  tff(c_189, plain, (![B_96, A_97]: (k3_xboole_0(B_96, A_97)=k3_xboole_0(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.86  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.86  tff(c_204, plain, (![B_96, A_97]: (r1_tarski(k3_xboole_0(B_96, A_97), A_97))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 4.62/1.86  tff(c_485, plain, (![A_129, B_130]: (r1_tarski(k1_tarski(A_129), k2_tarski(A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_473, c_204])).
% 4.62/1.86  tff(c_108, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.86  tff(c_1952, plain, (![A_184, C_185, B_186]: (r1_tarski(A_184, C_185) | ~r1_tarski(B_186, C_185) | ~r1_tarski(A_184, B_186))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.62/1.86  tff(c_2164, plain, (![A_195]: (r1_tarski(A_195, k2_tarski('#skF_9', '#skF_10')) | ~r1_tarski(A_195, k2_tarski('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_108, c_1952])).
% 4.62/1.86  tff(c_2190, plain, (r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_485, c_2164])).
% 4.62/1.86  tff(c_26, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.62/1.86  tff(c_2206, plain, (k3_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_2190, c_26])).
% 4.62/1.86  tff(c_245, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=A_109 | ~r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.62/1.86  tff(c_1040, plain, (![A_162, B_163]: (k3_xboole_0(k3_xboole_0(A_162, B_163), A_162)=k3_xboole_0(A_162, B_163))), inference(resolution, [status(thm)], [c_22, c_245])).
% 4.62/1.86  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.86  tff(c_284, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.86  tff(c_296, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_284])).
% 4.62/1.86  tff(c_1052, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k3_xboole_0(A_162, B_163))=k4_xboole_0(A_162, k3_xboole_0(A_162, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_296])).
% 4.62/1.86  tff(c_1119, plain, (![A_162, B_163]: (k4_xboole_0(A_162, k3_xboole_0(A_162, B_163))=k4_xboole_0(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1052])).
% 4.62/1.86  tff(c_3858, plain, (k4_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2206, c_1119])).
% 4.62/1.86  tff(c_3934, plain, (k4_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_599, c_3858])).
% 4.62/1.86  tff(c_80, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.86  tff(c_98, plain, (![B_77, C_78]: (k4_xboole_0(k2_tarski(B_77, B_77), C_78)=k1_tarski(B_77) | r2_hidden(B_77, C_78))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.62/1.86  tff(c_109, plain, (![B_77, C_78]: (k4_xboole_0(k1_tarski(B_77), C_78)=k1_tarski(B_77) | r2_hidden(B_77, C_78))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98])).
% 4.62/1.86  tff(c_3952, plain, (k1_tarski('#skF_7')=k1_xboole_0 | r2_hidden('#skF_7', k2_tarski('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_3934, c_109])).
% 4.62/1.86  tff(c_3964, plain, (r2_hidden('#skF_7', k2_tarski('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_2682, c_3952])).
% 4.62/1.86  tff(c_60, plain, (![D_43, B_39, A_38]: (D_43=B_39 | D_43=A_38 | ~r2_hidden(D_43, k2_tarski(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.86  tff(c_3971, plain, ('#skF_7'='#skF_10' | '#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_3964, c_60])).
% 4.62/1.86  tff(c_3975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_104, c_3971])).
% 4.62/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.86  
% 4.62/1.86  Inference rules
% 4.62/1.86  ----------------------
% 4.62/1.86  #Ref     : 0
% 4.62/1.86  #Sup     : 939
% 4.62/1.86  #Fact    : 0
% 4.62/1.86  #Define  : 0
% 4.62/1.86  #Split   : 1
% 4.62/1.86  #Chain   : 0
% 4.62/1.86  #Close   : 0
% 4.62/1.86  
% 4.62/1.86  Ordering : KBO
% 4.62/1.86  
% 4.62/1.86  Simplification rules
% 4.62/1.86  ----------------------
% 4.62/1.86  #Subsume      : 41
% 4.62/1.86  #Demod        : 745
% 4.62/1.86  #Tautology    : 650
% 4.62/1.86  #SimpNegUnit  : 10
% 4.62/1.86  #BackRed      : 2
% 4.62/1.86  
% 4.62/1.86  #Partial instantiations: 0
% 4.62/1.86  #Strategies tried      : 1
% 4.62/1.86  
% 4.62/1.86  Timing (in seconds)
% 4.62/1.86  ----------------------
% 4.62/1.87  Preprocessing        : 0.37
% 4.62/1.87  Parsing              : 0.19
% 4.62/1.87  CNF conversion       : 0.03
% 4.62/1.87  Main loop            : 0.80
% 4.62/1.87  Inferencing          : 0.23
% 4.62/1.87  Reduction            : 0.35
% 4.62/1.87  Demodulation         : 0.28
% 4.62/1.87  BG Simplification    : 0.03
% 4.62/1.87  Subsumption          : 0.13
% 4.62/1.87  Abstraction          : 0.04
% 4.62/1.87  MUC search           : 0.00
% 4.62/1.87  Cooper               : 0.00
% 4.62/1.87  Total                : 1.19
% 4.62/1.87  Index Insertion      : 0.00
% 4.62/1.87  Index Deletion       : 0.00
% 4.62/1.87  Index Matching       : 0.00
% 4.62/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
