%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:02 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 104 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 110 expanded)
%              Number of equality atoms :   59 (  88 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1368,plain,(
    ! [B_155,E_152,C_153,D_154,A_151] : k2_xboole_0(k2_enumset1(A_151,B_155,C_153,D_154),k1_tarski(E_152)) = k3_enumset1(A_151,B_155,C_153,D_154,E_152) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1377,plain,(
    ! [A_41,B_42,C_43,E_152] : k3_enumset1(A_41,A_41,B_42,C_43,E_152) = k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(E_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1368])).

tff(c_1557,plain,(
    ! [A_168,B_169,C_170,E_171] : k2_xboole_0(k1_enumset1(A_168,B_169,C_170),k1_tarski(E_171)) = k2_enumset1(A_168,B_169,C_170,E_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1377])).

tff(c_1596,plain,(
    ! [A_39,B_40,E_171] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(E_171)) = k2_enumset1(A_39,A_39,B_40,E_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1557])).

tff(c_1600,plain,(
    ! [A_172,B_173,E_174] : k2_xboole_0(k2_tarski(A_172,B_173),k1_tarski(E_174)) = k1_enumset1(A_172,B_173,E_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1596])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_157])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_559,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_571,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_559])).

tff(c_613,plain,(
    ! [A_112] : k4_xboole_0(A_112,k1_xboole_0) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_571])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_626,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k3_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_12])).

tff(c_636,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_626])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_583,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_559])).

tff(c_704,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_583])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_157])).

tff(c_568,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_559])).

tff(c_705,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_568])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_775,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_16])).

tff(c_781,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_775])).

tff(c_1606,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_781])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1643,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_20])).

tff(c_390,plain,(
    ! [C_102,B_103,A_104] : k1_enumset1(C_102,B_103,A_104) = k1_enumset1(A_104,B_103,C_102) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_418,plain,(
    ! [C_102,B_103] : k1_enumset1(C_102,B_103,B_103) = k2_tarski(B_103,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_50])).

tff(c_1183,plain,(
    ! [E_133,C_134,B_135,A_136] :
      ( E_133 = C_134
      | E_133 = B_135
      | E_133 = A_136
      | ~ r2_hidden(E_133,k1_enumset1(A_136,B_135,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1198,plain,(
    ! [E_133,B_103,C_102] :
      ( E_133 = B_103
      | E_133 = B_103
      | E_133 = C_102
      | ~ r2_hidden(E_133,k2_tarski(B_103,C_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_1183])).

tff(c_1667,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1643,c_1198])).

tff(c_1674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66,c_66,c_1667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.61  
% 3.43/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.62  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.43/1.62  
% 3.43/1.62  %Foreground sorts:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Background operators:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Foreground operators:
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.43/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.43/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.43/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.43/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.43/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.43/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.43/1.62  
% 3.75/1.63  tff(f_90, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.75/1.63  tff(f_70, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.75/1.63  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.75/1.63  tff(f_72, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.75/1.63  tff(f_64, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.75/1.63  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.75/1.63  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.75/1.63  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.75/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.75/1.63  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.75/1.63  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.75/1.63  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.75/1.63  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.75/1.63  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.75/1.63  tff(f_62, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.75/1.63  tff(c_64, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.63  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.63  tff(c_52, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.63  tff(c_50, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.75/1.63  tff(c_54, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.75/1.63  tff(c_1368, plain, (![B_155, E_152, C_153, D_154, A_151]: (k2_xboole_0(k2_enumset1(A_151, B_155, C_153, D_154), k1_tarski(E_152))=k3_enumset1(A_151, B_155, C_153, D_154, E_152))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.75/1.63  tff(c_1377, plain, (![A_41, B_42, C_43, E_152]: (k3_enumset1(A_41, A_41, B_42, C_43, E_152)=k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(E_152)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1368])).
% 3.75/1.63  tff(c_1557, plain, (![A_168, B_169, C_170, E_171]: (k2_xboole_0(k1_enumset1(A_168, B_169, C_170), k1_tarski(E_171))=k2_enumset1(A_168, B_169, C_170, E_171))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1377])).
% 3.75/1.63  tff(c_1596, plain, (![A_39, B_40, E_171]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(E_171))=k2_enumset1(A_39, A_39, B_40, E_171))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1557])).
% 3.75/1.63  tff(c_1600, plain, (![A_172, B_173, E_174]: (k2_xboole_0(k2_tarski(A_172, B_173), k1_tarski(E_174))=k1_enumset1(A_172, B_173, E_174))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1596])).
% 3.75/1.63  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.75/1.63  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.75/1.63  tff(c_157, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.63  tff(c_166, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_157])).
% 3.75/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.63  tff(c_171, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 3.75/1.63  tff(c_559, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.63  tff(c_571, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_559])).
% 3.75/1.63  tff(c_613, plain, (![A_112]: (k4_xboole_0(A_112, k1_xboole_0)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_571])).
% 3.75/1.63  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.75/1.63  tff(c_626, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k3_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_613, c_12])).
% 3.75/1.63  tff(c_636, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_626])).
% 3.75/1.63  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.75/1.63  tff(c_583, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_559])).
% 3.75/1.63  tff(c_704, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_636, c_583])).
% 3.75/1.63  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.63  tff(c_164, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_68, c_157])).
% 3.75/1.63  tff(c_568, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_559])).
% 3.75/1.63  tff(c_705, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_704, c_568])).
% 3.75/1.63  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.63  tff(c_775, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_705, c_16])).
% 3.75/1.63  tff(c_781, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_775])).
% 3.75/1.63  tff(c_1606, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1600, c_781])).
% 3.75/1.63  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.75/1.63  tff(c_1643, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1606, c_20])).
% 3.75/1.63  tff(c_390, plain, (![C_102, B_103, A_104]: (k1_enumset1(C_102, B_103, A_104)=k1_enumset1(A_104, B_103, C_102))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.75/1.63  tff(c_418, plain, (![C_102, B_103]: (k1_enumset1(C_102, B_103, B_103)=k2_tarski(B_103, C_102))), inference(superposition, [status(thm), theory('equality')], [c_390, c_50])).
% 3.75/1.63  tff(c_1183, plain, (![E_133, C_134, B_135, A_136]: (E_133=C_134 | E_133=B_135 | E_133=A_136 | ~r2_hidden(E_133, k1_enumset1(A_136, B_135, C_134)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.75/1.63  tff(c_1198, plain, (![E_133, B_103, C_102]: (E_133=B_103 | E_133=B_103 | E_133=C_102 | ~r2_hidden(E_133, k2_tarski(B_103, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_1183])).
% 3.75/1.63  tff(c_1667, plain, ('#skF_3'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1643, c_1198])).
% 3.75/1.63  tff(c_1674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66, c_66, c_1667])).
% 3.75/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  
% 3.75/1.63  Inference rules
% 3.75/1.63  ----------------------
% 3.75/1.63  #Ref     : 0
% 3.75/1.63  #Sup     : 410
% 3.75/1.63  #Fact    : 0
% 3.75/1.63  #Define  : 0
% 3.75/1.63  #Split   : 0
% 3.75/1.63  #Chain   : 0
% 3.75/1.63  #Close   : 0
% 3.75/1.63  
% 3.75/1.63  Ordering : KBO
% 3.75/1.63  
% 3.75/1.63  Simplification rules
% 3.75/1.63  ----------------------
% 3.75/1.63  #Subsume      : 58
% 3.75/1.63  #Demod        : 231
% 3.75/1.63  #Tautology    : 271
% 3.75/1.63  #SimpNegUnit  : 1
% 3.75/1.63  #BackRed      : 1
% 3.75/1.63  
% 3.75/1.63  #Partial instantiations: 0
% 3.75/1.63  #Strategies tried      : 1
% 3.75/1.63  
% 3.75/1.63  Timing (in seconds)
% 3.75/1.63  ----------------------
% 3.75/1.64  Preprocessing        : 0.35
% 3.75/1.64  Parsing              : 0.18
% 3.75/1.64  CNF conversion       : 0.03
% 3.75/1.64  Main loop            : 0.49
% 3.75/1.64  Inferencing          : 0.16
% 3.75/1.64  Reduction            : 0.20
% 3.75/1.64  Demodulation         : 0.16
% 3.75/1.64  BG Simplification    : 0.03
% 3.75/1.64  Subsumption          : 0.08
% 3.75/1.64  Abstraction          : 0.03
% 3.75/1.64  MUC search           : 0.00
% 3.75/1.64  Cooper               : 0.00
% 3.75/1.64  Total                : 0.88
% 3.75/1.64  Index Insertion      : 0.00
% 3.75/1.64  Index Deletion       : 0.00
% 3.75/1.64  Index Matching       : 0.00
% 3.75/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
