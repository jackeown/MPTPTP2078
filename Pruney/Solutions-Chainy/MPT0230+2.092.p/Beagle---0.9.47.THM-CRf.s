%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:07 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 107 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :   79 ( 117 expanded)
%              Number of equality atoms :   64 (  93 expanded)
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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_60,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : k5_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47) = k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : k6_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53,G_54) = k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_339,plain,(
    ! [H_140,G_143,D_145,A_142,B_141,E_139,C_138,F_144] : k2_xboole_0(k5_enumset1(A_142,B_141,C_138,D_145,E_139,F_144,G_143),k1_tarski(H_140)) = k6_enumset1(A_142,B_141,C_138,D_145,E_139,F_144,G_143,H_140) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_348,plain,(
    ! [H_140,B_43,A_42,D_45,E_46,C_44,F_47] : k6_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47,H_140) = k2_xboole_0(k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47),k1_tarski(H_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_339])).

tff(c_352,plain,(
    ! [B_148,H_150,C_152,A_149,D_147,E_146,F_151] : k2_xboole_0(k4_enumset1(A_149,B_148,C_152,D_147,E_146,F_151),k1_tarski(H_150)) = k5_enumset1(A_149,B_148,C_152,D_147,E_146,F_151,H_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_348])).

tff(c_361,plain,(
    ! [C_39,B_38,H_150,A_37,D_40,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,H_150) = k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k1_tarski(H_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_352])).

tff(c_365,plain,(
    ! [D_155,H_158,E_156,A_153,C_157,B_154] : k2_xboole_0(k3_enumset1(A_153,B_154,C_157,D_155,E_156),k1_tarski(H_158)) = k4_enumset1(A_153,B_154,C_157,D_155,E_156,H_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_361])).

tff(c_374,plain,(
    ! [D_36,H_158,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,H_158) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(H_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_365])).

tff(c_378,plain,(
    ! [C_160,D_161,A_159,B_163,H_162] : k2_xboole_0(k2_enumset1(A_159,B_163,C_160,D_161),k1_tarski(H_162)) = k3_enumset1(A_159,B_163,C_160,D_161,H_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_374])).

tff(c_387,plain,(
    ! [A_30,B_31,C_32,H_162] : k3_enumset1(A_30,A_30,B_31,C_32,H_162) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(H_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_378])).

tff(c_392,plain,(
    ! [A_168,B_169,C_170,H_171] : k2_xboole_0(k1_enumset1(A_168,B_169,C_170),k1_tarski(H_171)) = k2_enumset1(A_168,B_169,C_170,H_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_387])).

tff(c_401,plain,(
    ! [A_28,B_29,H_171] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(H_171)) = k2_enumset1(A_28,A_28,B_29,H_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_392])).

tff(c_405,plain,(
    ! [A_172,B_173,H_174] : k2_xboole_0(k2_tarski(A_172,B_173),k1_tarski(H_174)) = k1_enumset1(A_172,B_173,H_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_401])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_14,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_149,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_149])).

tff(c_161,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_191,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_203,plain,(
    ! [B_2] : k5_xboole_0(B_2,k1_xboole_0) = k2_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_191])).

tff(c_206,plain,(
    ! [B_2] : k5_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_203])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_133,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_126])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_168,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_165])).

tff(c_200,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_191])).

tff(c_249,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_200])).

tff(c_411,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_249])).

tff(c_20,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_439,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_20])).

tff(c_254,plain,(
    ! [E_95,C_96,B_97,A_98] :
      ( E_95 = C_96
      | E_95 = B_97
      | E_95 = A_98
      | ~ r2_hidden(E_95,k1_enumset1(A_98,B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_257,plain,(
    ! [E_95,B_29,A_28] :
      ( E_95 = B_29
      | E_95 = A_28
      | E_95 = A_28
      | ~ r2_hidden(E_95,k2_tarski(A_28,B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_254])).

tff(c_449,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_439,c_257])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_58,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.57/1.37  
% 2.57/1.39  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.57/1.39  tff(f_68, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.57/1.39  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.57/1.39  tff(f_70, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.57/1.39  tff(f_72, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.57/1.39  tff(f_74, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.57/1.39  tff(f_76, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.57/1.39  tff(f_62, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.57/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.39  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.57/1.39  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.57/1.39  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.57/1.39  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.39  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.57/1.39  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.57/1.39  tff(c_60, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_58, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_48, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.39  tff(c_46, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.39  tff(c_50, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.57/1.39  tff(c_52, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.57/1.39  tff(c_54, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (k5_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47)=k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.39  tff(c_56, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (k6_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53, G_54)=k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.39  tff(c_339, plain, (![H_140, G_143, D_145, A_142, B_141, E_139, C_138, F_144]: (k2_xboole_0(k5_enumset1(A_142, B_141, C_138, D_145, E_139, F_144, G_143), k1_tarski(H_140))=k6_enumset1(A_142, B_141, C_138, D_145, E_139, F_144, G_143, H_140))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.39  tff(c_348, plain, (![H_140, B_43, A_42, D_45, E_46, C_44, F_47]: (k6_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47, H_140)=k2_xboole_0(k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47), k1_tarski(H_140)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_339])).
% 2.57/1.39  tff(c_352, plain, (![B_148, H_150, C_152, A_149, D_147, E_146, F_151]: (k2_xboole_0(k4_enumset1(A_149, B_148, C_152, D_147, E_146, F_151), k1_tarski(H_150))=k5_enumset1(A_149, B_148, C_152, D_147, E_146, F_151, H_150))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_348])).
% 2.57/1.39  tff(c_361, plain, (![C_39, B_38, H_150, A_37, D_40, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, H_150)=k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k1_tarski(H_150)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_352])).
% 2.57/1.39  tff(c_365, plain, (![D_155, H_158, E_156, A_153, C_157, B_154]: (k2_xboole_0(k3_enumset1(A_153, B_154, C_157, D_155, E_156), k1_tarski(H_158))=k4_enumset1(A_153, B_154, C_157, D_155, E_156, H_158))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_361])).
% 2.57/1.39  tff(c_374, plain, (![D_36, H_158, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, H_158)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(H_158)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_365])).
% 2.57/1.39  tff(c_378, plain, (![C_160, D_161, A_159, B_163, H_162]: (k2_xboole_0(k2_enumset1(A_159, B_163, C_160, D_161), k1_tarski(H_162))=k3_enumset1(A_159, B_163, C_160, D_161, H_162))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_374])).
% 2.57/1.39  tff(c_387, plain, (![A_30, B_31, C_32, H_162]: (k3_enumset1(A_30, A_30, B_31, C_32, H_162)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(H_162)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_378])).
% 2.57/1.39  tff(c_392, plain, (![A_168, B_169, C_170, H_171]: (k2_xboole_0(k1_enumset1(A_168, B_169, C_170), k1_tarski(H_171))=k2_enumset1(A_168, B_169, C_170, H_171))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_387])).
% 2.57/1.39  tff(c_401, plain, (![A_28, B_29, H_171]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(H_171))=k2_enumset1(A_28, A_28, B_29, H_171))), inference(superposition, [status(thm), theory('equality')], [c_46, c_392])).
% 2.57/1.39  tff(c_405, plain, (![A_172, B_173, H_174]: (k2_xboole_0(k2_tarski(A_172, B_173), k1_tarski(H_174))=k1_enumset1(A_172, B_173, H_174))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_401])).
% 2.57/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.39  tff(c_84, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.39  tff(c_92, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.57/1.39  tff(c_14, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.39  tff(c_126, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.39  tff(c_134, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_126])).
% 2.57/1.39  tff(c_149, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_158, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_134, c_149])).
% 2.57/1.39  tff(c_161, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_158])).
% 2.57/1.39  tff(c_191, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.39  tff(c_203, plain, (![B_2]: (k5_xboole_0(B_2, k1_xboole_0)=k2_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_161, c_191])).
% 2.57/1.39  tff(c_206, plain, (![B_2]: (k5_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_203])).
% 2.57/1.39  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_133, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_62, c_126])).
% 2.57/1.39  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_165, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 2.57/1.39  tff(c_168, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_165])).
% 2.57/1.39  tff(c_200, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_191])).
% 2.57/1.39  tff(c_249, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_200])).
% 2.57/1.39  tff(c_411, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_405, c_249])).
% 2.57/1.39  tff(c_20, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.39  tff(c_439, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_20])).
% 2.57/1.39  tff(c_254, plain, (![E_95, C_96, B_97, A_98]: (E_95=C_96 | E_95=B_97 | E_95=A_98 | ~r2_hidden(E_95, k1_enumset1(A_98, B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.39  tff(c_257, plain, (![E_95, B_29, A_28]: (E_95=B_29 | E_95=A_28 | E_95=A_28 | ~r2_hidden(E_95, k2_tarski(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_254])).
% 2.57/1.39  tff(c_449, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_439, c_257])).
% 2.57/1.39  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_58, c_449])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 92
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 1
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 0
% 2.57/1.39  #Demod        : 18
% 2.57/1.39  #Tautology    : 65
% 2.57/1.39  #SimpNegUnit  : 1
% 2.57/1.39  #BackRed      : 0
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.39  Preprocessing        : 0.32
% 2.57/1.39  Parsing              : 0.16
% 2.57/1.39  CNF conversion       : 0.02
% 2.57/1.39  Main loop            : 0.26
% 2.57/1.39  Inferencing          : 0.10
% 2.57/1.39  Reduction            : 0.08
% 2.57/1.39  Demodulation         : 0.06
% 2.57/1.39  BG Simplification    : 0.02
% 2.57/1.39  Subsumption          : 0.05
% 2.57/1.39  Abstraction          : 0.02
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.40  Total                : 0.61
% 2.57/1.40  Index Insertion      : 0.00
% 2.57/1.40  Index Deletion       : 0.00
% 2.57/1.40  Index Matching       : 0.00
% 2.57/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
