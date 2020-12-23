%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   76 (  95 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :   68 (  97 expanded)
%              Number of equality atoms :   58 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32,D_33] : k3_enumset1(A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [D_37,A_34,B_35,C_36,E_38] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,E_38) = k3_enumset1(A_34,B_35,C_36,D_37,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_242,plain,(
    ! [G_107,D_108,F_109,E_110,A_104,C_106,B_105] : k6_enumset1(A_104,A_104,B_105,C_106,D_108,E_110,F_109,G_107) = k5_enumset1(A_104,B_105,C_106,D_108,E_110,F_109,G_107) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [A_46,E_50,B_47,C_48,D_49,F_51] : k6_enumset1(A_46,A_46,A_46,B_47,C_48,D_49,E_50,F_51) = k4_enumset1(A_46,B_47,C_48,D_49,E_50,F_51) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    ! [G_107,D_108,F_109,E_110,C_106,B_105] : k5_enumset1(B_105,B_105,C_106,D_108,E_110,F_109,G_107) = k4_enumset1(B_105,C_106,D_108,E_110,F_109,G_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_50])).

tff(c_48,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,G_45) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_287,plain,(
    ! [C_140,A_138,B_136,E_137,G_135,F_133,H_134,D_139] : k2_xboole_0(k5_enumset1(A_138,B_136,C_140,D_139,E_137,F_133,G_135),k1_tarski(H_134)) = k6_enumset1(A_138,B_136,C_140,D_139,E_137,F_133,G_135,H_134) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,(
    ! [G_107,D_108,F_109,E_110,C_106,B_105,H_134] : k6_enumset1(B_105,B_105,C_106,D_108,E_110,F_109,G_107,H_134) = k2_xboole_0(k4_enumset1(B_105,C_106,D_108,E_110,F_109,G_107),k1_tarski(H_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_287])).

tff(c_301,plain,(
    ! [C_151,D_147,G_146,F_148,E_150,H_149,B_145] : k2_xboole_0(k4_enumset1(B_145,C_151,D_147,E_150,F_148,G_146),k1_tarski(H_149)) = k5_enumset1(B_145,C_151,D_147,E_150,F_148,G_146,H_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_296])).

tff(c_310,plain,(
    ! [D_37,A_34,B_35,C_36,H_149,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,H_149) = k2_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38),k1_tarski(H_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_301])).

tff(c_314,plain,(
    ! [A_152,B_155,D_153,H_156,C_157,E_154] : k2_xboole_0(k3_enumset1(A_152,B_155,C_157,D_153,E_154),k1_tarski(H_156)) = k4_enumset1(A_152,B_155,C_157,D_153,E_154,H_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_310])).

tff(c_323,plain,(
    ! [D_33,A_30,C_32,B_31,H_156] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,H_156) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k1_tarski(H_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_314])).

tff(c_327,plain,(
    ! [C_158,D_162,H_159,A_161,B_160] : k2_xboole_0(k2_enumset1(A_161,B_160,C_158,D_162),k1_tarski(H_159)) = k3_enumset1(A_161,B_160,C_158,D_162,H_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323])).

tff(c_336,plain,(
    ! [A_27,B_28,C_29,H_159] : k3_enumset1(A_27,A_27,B_28,C_29,H_159) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k1_tarski(H_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_327])).

tff(c_341,plain,(
    ! [A_167,B_168,C_169,H_170] : k2_xboole_0(k1_enumset1(A_167,B_168,C_169),k1_tarski(H_170)) = k2_enumset1(A_167,B_168,C_169,H_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_336])).

tff(c_350,plain,(
    ! [A_25,B_26,H_170] : k2_xboole_0(k2_tarski(A_25,B_26),k1_tarski(H_170)) = k2_enumset1(A_25,A_25,B_26,H_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_341])).

tff(c_354,plain,(
    ! [A_171,B_172,H_173] : k2_xboole_0(k2_tarski(A_171,B_172),k1_tarski(H_173)) = k1_enumset1(A_171,B_172,H_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_350])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_124,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2])).

tff(c_153,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_10])).

tff(c_161,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_360,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_161])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_388,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_14])).

tff(c_185,plain,(
    ! [E_84,C_85,B_86,A_87] :
      ( E_84 = C_85
      | E_84 = B_86
      | E_84 = A_87
      | ~ r2_hidden(E_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_188,plain,(
    ! [E_84,B_26,A_25] :
      ( E_84 = B_26
      | E_84 = A_25
      | E_84 = A_25
      | ~ r2_hidden(E_84,k2_tarski(A_25,B_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_185])).

tff(c_397,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_388,c_188])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_52,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  
% 2.49/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.41  
% 2.49/1.41  %Foreground sorts:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Background operators:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Foreground operators:
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.49/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.49/1.41  
% 2.49/1.43  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.49/1.43  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.49/1.43  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.49/1.43  tff(f_62, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.49/1.43  tff(f_64, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.49/1.43  tff(f_66, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.49/1.43  tff(f_68, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 2.49/1.43  tff(f_54, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.49/1.43  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.49/1.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.49/1.43  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.49/1.43  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.49/1.43  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.49/1.43  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.49/1.43  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.49/1.43  tff(c_52, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.49/1.43  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.43  tff(c_40, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.43  tff(c_44, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.49/1.43  tff(c_46, plain, (![D_37, A_34, B_35, C_36, E_38]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, E_38)=k3_enumset1(A_34, B_35, C_36, D_37, E_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.43  tff(c_242, plain, (![G_107, D_108, F_109, E_110, A_104, C_106, B_105]: (k6_enumset1(A_104, A_104, B_105, C_106, D_108, E_110, F_109, G_107)=k5_enumset1(A_104, B_105, C_106, D_108, E_110, F_109, G_107))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.43  tff(c_50, plain, (![A_46, E_50, B_47, C_48, D_49, F_51]: (k6_enumset1(A_46, A_46, A_46, B_47, C_48, D_49, E_50, F_51)=k4_enumset1(A_46, B_47, C_48, D_49, E_50, F_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.43  tff(c_249, plain, (![G_107, D_108, F_109, E_110, C_106, B_105]: (k5_enumset1(B_105, B_105, C_106, D_108, E_110, F_109, G_107)=k4_enumset1(B_105, C_106, D_108, E_110, F_109, G_107))), inference(superposition, [status(thm), theory('equality')], [c_242, c_50])).
% 2.49/1.43  tff(c_48, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, G_45)=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.43  tff(c_287, plain, (![C_140, A_138, B_136, E_137, G_135, F_133, H_134, D_139]: (k2_xboole_0(k5_enumset1(A_138, B_136, C_140, D_139, E_137, F_133, G_135), k1_tarski(H_134))=k6_enumset1(A_138, B_136, C_140, D_139, E_137, F_133, G_135, H_134))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.43  tff(c_296, plain, (![G_107, D_108, F_109, E_110, C_106, B_105, H_134]: (k6_enumset1(B_105, B_105, C_106, D_108, E_110, F_109, G_107, H_134)=k2_xboole_0(k4_enumset1(B_105, C_106, D_108, E_110, F_109, G_107), k1_tarski(H_134)))), inference(superposition, [status(thm), theory('equality')], [c_249, c_287])).
% 2.49/1.43  tff(c_301, plain, (![C_151, D_147, G_146, F_148, E_150, H_149, B_145]: (k2_xboole_0(k4_enumset1(B_145, C_151, D_147, E_150, F_148, G_146), k1_tarski(H_149))=k5_enumset1(B_145, C_151, D_147, E_150, F_148, G_146, H_149))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_296])).
% 2.49/1.43  tff(c_310, plain, (![D_37, A_34, B_35, C_36, H_149, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, H_149)=k2_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38), k1_tarski(H_149)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_301])).
% 2.49/1.43  tff(c_314, plain, (![A_152, B_155, D_153, H_156, C_157, E_154]: (k2_xboole_0(k3_enumset1(A_152, B_155, C_157, D_153, E_154), k1_tarski(H_156))=k4_enumset1(A_152, B_155, C_157, D_153, E_154, H_156))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_310])).
% 2.49/1.43  tff(c_323, plain, (![D_33, A_30, C_32, B_31, H_156]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, H_156)=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k1_tarski(H_156)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_314])).
% 2.49/1.43  tff(c_327, plain, (![C_158, D_162, H_159, A_161, B_160]: (k2_xboole_0(k2_enumset1(A_161, B_160, C_158, D_162), k1_tarski(H_159))=k3_enumset1(A_161, B_160, C_158, D_162, H_159))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323])).
% 2.49/1.43  tff(c_336, plain, (![A_27, B_28, C_29, H_159]: (k3_enumset1(A_27, A_27, B_28, C_29, H_159)=k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k1_tarski(H_159)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_327])).
% 2.49/1.43  tff(c_341, plain, (![A_167, B_168, C_169, H_170]: (k2_xboole_0(k1_enumset1(A_167, B_168, C_169), k1_tarski(H_170))=k2_enumset1(A_167, B_168, C_169, H_170))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_336])).
% 2.49/1.43  tff(c_350, plain, (![A_25, B_26, H_170]: (k2_xboole_0(k2_tarski(A_25, B_26), k1_tarski(H_170))=k2_enumset1(A_25, A_25, B_26, H_170))), inference(superposition, [status(thm), theory('equality')], [c_40, c_341])).
% 2.49/1.43  tff(c_354, plain, (![A_171, B_172, H_173]: (k2_xboole_0(k2_tarski(A_171, B_172), k1_tarski(H_173))=k1_enumset1(A_171, B_172, H_173))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_350])).
% 2.49/1.43  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.43  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.43  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.49/1.43  tff(c_124, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.43  tff(c_128, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.49/1.43  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.43  tff(c_150, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 2.49/1.43  tff(c_153, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_150])).
% 2.49/1.43  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.43  tff(c_158, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_10])).
% 2.49/1.43  tff(c_161, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 2.49/1.43  tff(c_360, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_354, c_161])).
% 2.49/1.43  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.43  tff(c_388, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_14])).
% 2.49/1.43  tff(c_185, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.43  tff(c_188, plain, (![E_84, B_26, A_25]: (E_84=B_26 | E_84=A_25 | E_84=A_25 | ~r2_hidden(E_84, k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_185])).
% 2.49/1.43  tff(c_397, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_388, c_188])).
% 2.49/1.43  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_52, c_397])).
% 2.49/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.43  
% 2.49/1.43  Inference rules
% 2.49/1.43  ----------------------
% 2.49/1.43  #Ref     : 0
% 2.49/1.43  #Sup     : 81
% 2.49/1.43  #Fact    : 0
% 2.49/1.43  #Define  : 0
% 2.49/1.43  #Split   : 0
% 2.49/1.43  #Chain   : 0
% 2.49/1.43  #Close   : 0
% 2.49/1.43  
% 2.49/1.43  Ordering : KBO
% 2.49/1.43  
% 2.49/1.43  Simplification rules
% 2.49/1.43  ----------------------
% 2.49/1.43  #Subsume      : 0
% 2.49/1.43  #Demod        : 14
% 2.49/1.43  #Tautology    : 57
% 2.49/1.43  #SimpNegUnit  : 1
% 2.49/1.43  #BackRed      : 0
% 2.49/1.43  
% 2.49/1.43  #Partial instantiations: 0
% 2.49/1.43  #Strategies tried      : 1
% 2.49/1.43  
% 2.49/1.43  Timing (in seconds)
% 2.49/1.43  ----------------------
% 2.49/1.43  Preprocessing        : 0.34
% 2.49/1.43  Parsing              : 0.18
% 2.49/1.43  CNF conversion       : 0.02
% 2.49/1.43  Main loop            : 0.24
% 2.49/1.43  Inferencing          : 0.10
% 2.49/1.43  Reduction            : 0.07
% 2.49/1.43  Demodulation         : 0.05
% 2.49/1.43  BG Simplification    : 0.02
% 2.49/1.43  Subsumption          : 0.04
% 2.49/1.43  Abstraction          : 0.02
% 2.49/1.43  MUC search           : 0.00
% 2.49/1.43  Cooper               : 0.00
% 2.49/1.43  Total                : 0.62
% 2.49/1.43  Index Insertion      : 0.00
% 2.49/1.43  Index Deletion       : 0.00
% 2.49/1.43  Index Matching       : 0.00
% 2.49/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
