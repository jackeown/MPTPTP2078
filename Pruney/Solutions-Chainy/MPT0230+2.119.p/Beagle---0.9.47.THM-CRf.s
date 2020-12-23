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
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   74 (  89 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 (  91 expanded)
%              Number of equality atoms :   56 (  77 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

tff(c_48,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44) = k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [D_48,C_47,A_45,B_46,G_51,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,G_51) = k5_enumset1(A_45,B_46,C_47,D_48,E_49,F_50,G_51) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_270,plain,(
    ! [H_128,G_129,F_127,A_132,D_133,C_134,E_131,B_130] : k2_xboole_0(k5_enumset1(A_132,B_130,C_134,D_133,E_131,F_127,G_129),k1_tarski(H_128)) = k6_enumset1(A_132,B_130,C_134,D_133,E_131,F_127,G_129,H_128) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_279,plain,(
    ! [H_128,E_43,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,H_128) = k2_xboole_0(k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44),k1_tarski(H_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_270])).

tff(c_283,plain,(
    ! [C_137,B_136,E_141,F_140,H_138,D_139,A_135] : k2_xboole_0(k4_enumset1(A_135,B_136,C_137,D_139,E_141,F_140),k1_tarski(H_138)) = k5_enumset1(A_135,B_136,C_137,D_139,E_141,F_140,H_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_279])).

tff(c_292,plain,(
    ! [D_37,A_34,B_35,C_36,H_138,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,H_138) = k2_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38),k1_tarski(H_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_283])).

tff(c_296,plain,(
    ! [H_146,C_147,E_144,A_142,D_143,B_145] : k2_xboole_0(k3_enumset1(A_142,B_145,C_147,D_143,E_144),k1_tarski(H_146)) = k4_enumset1(A_142,B_145,C_147,D_143,E_144,H_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_292])).

tff(c_305,plain,(
    ! [H_146,D_33,A_30,C_32,B_31] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,H_146) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k1_tarski(H_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_296])).

tff(c_310,plain,(
    ! [H_154,C_152,A_155,D_156,B_153] : k2_xboole_0(k2_enumset1(A_155,B_153,C_152,D_156),k1_tarski(H_154)) = k3_enumset1(A_155,B_153,C_152,D_156,H_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_305])).

tff(c_319,plain,(
    ! [A_27,B_28,C_29,H_154] : k3_enumset1(A_27,A_27,B_28,C_29,H_154) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k1_tarski(H_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_310])).

tff(c_323,plain,(
    ! [A_157,B_158,C_159,H_160] : k2_xboole_0(k1_enumset1(A_157,B_158,C_159),k1_tarski(H_160)) = k2_enumset1(A_157,B_158,C_159,H_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_319])).

tff(c_332,plain,(
    ! [A_25,B_26,H_160] : k2_xboole_0(k2_tarski(A_25,B_26),k1_tarski(H_160)) = k2_enumset1(A_25,A_25,B_26,H_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_323])).

tff(c_336,plain,(
    ! [A_161,B_162,H_163] : k2_xboole_0(k2_tarski(A_161,B_162),k1_tarski(H_163)) = k1_enumset1(A_161,B_162,H_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_332])).

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

tff(c_342,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_161])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_370,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_14])).

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

tff(c_379,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_370,c_188])).

tff(c_383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_52,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.56/1.33  
% 2.56/1.35  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.56/1.35  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.56/1.35  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.56/1.35  tff(f_62, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.56/1.35  tff(f_64, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.56/1.35  tff(f_66, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.56/1.35  tff(f_68, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.56/1.35  tff(f_54, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.56/1.35  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.56/1.35  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.56/1.35  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.56/1.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/1.35  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.56/1.35  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.56/1.35  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.35  tff(c_52, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.35  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.35  tff(c_40, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.56/1.35  tff(c_44, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.35  tff(c_46, plain, (![D_37, A_34, B_35, C_36, E_38]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, E_38)=k3_enumset1(A_34, B_35, C_36, D_37, E_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.35  tff(c_48, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44)=k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.35  tff(c_50, plain, (![D_48, C_47, A_45, B_46, G_51, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, G_51)=k5_enumset1(A_45, B_46, C_47, D_48, E_49, F_50, G_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.56/1.35  tff(c_270, plain, (![H_128, G_129, F_127, A_132, D_133, C_134, E_131, B_130]: (k2_xboole_0(k5_enumset1(A_132, B_130, C_134, D_133, E_131, F_127, G_129), k1_tarski(H_128))=k6_enumset1(A_132, B_130, C_134, D_133, E_131, F_127, G_129, H_128))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.56/1.35  tff(c_279, plain, (![H_128, E_43, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, H_128)=k2_xboole_0(k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44), k1_tarski(H_128)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_270])).
% 2.56/1.35  tff(c_283, plain, (![C_137, B_136, E_141, F_140, H_138, D_139, A_135]: (k2_xboole_0(k4_enumset1(A_135, B_136, C_137, D_139, E_141, F_140), k1_tarski(H_138))=k5_enumset1(A_135, B_136, C_137, D_139, E_141, F_140, H_138))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_279])).
% 2.56/1.35  tff(c_292, plain, (![D_37, A_34, B_35, C_36, H_138, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, H_138)=k2_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38), k1_tarski(H_138)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_283])).
% 2.56/1.35  tff(c_296, plain, (![H_146, C_147, E_144, A_142, D_143, B_145]: (k2_xboole_0(k3_enumset1(A_142, B_145, C_147, D_143, E_144), k1_tarski(H_146))=k4_enumset1(A_142, B_145, C_147, D_143, E_144, H_146))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_292])).
% 2.56/1.35  tff(c_305, plain, (![H_146, D_33, A_30, C_32, B_31]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, H_146)=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k1_tarski(H_146)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_296])).
% 2.56/1.35  tff(c_310, plain, (![H_154, C_152, A_155, D_156, B_153]: (k2_xboole_0(k2_enumset1(A_155, B_153, C_152, D_156), k1_tarski(H_154))=k3_enumset1(A_155, B_153, C_152, D_156, H_154))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_305])).
% 2.56/1.35  tff(c_319, plain, (![A_27, B_28, C_29, H_154]: (k3_enumset1(A_27, A_27, B_28, C_29, H_154)=k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k1_tarski(H_154)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_310])).
% 2.56/1.35  tff(c_323, plain, (![A_157, B_158, C_159, H_160]: (k2_xboole_0(k1_enumset1(A_157, B_158, C_159), k1_tarski(H_160))=k2_enumset1(A_157, B_158, C_159, H_160))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_319])).
% 2.56/1.35  tff(c_332, plain, (![A_25, B_26, H_160]: (k2_xboole_0(k2_tarski(A_25, B_26), k1_tarski(H_160))=k2_enumset1(A_25, A_25, B_26, H_160))), inference(superposition, [status(thm), theory('equality')], [c_40, c_323])).
% 2.56/1.35  tff(c_336, plain, (![A_161, B_162, H_163]: (k2_xboole_0(k2_tarski(A_161, B_162), k1_tarski(H_163))=k1_enumset1(A_161, B_162, H_163))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_332])).
% 2.56/1.35  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.35  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.35  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.35  tff(c_124, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.35  tff(c_128, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.56/1.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.35  tff(c_150, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 2.56/1.35  tff(c_153, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_150])).
% 2.56/1.35  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.35  tff(c_158, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_10])).
% 2.56/1.35  tff(c_161, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 2.56/1.35  tff(c_342, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_336, c_161])).
% 2.56/1.35  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.35  tff(c_370, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_14])).
% 2.56/1.35  tff(c_185, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.35  tff(c_188, plain, (![E_84, B_26, A_25]: (E_84=B_26 | E_84=A_25 | E_84=A_25 | ~r2_hidden(E_84, k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_185])).
% 2.56/1.35  tff(c_379, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_370, c_188])).
% 2.56/1.35  tff(c_383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_52, c_379])).
% 2.56/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  Inference rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Ref     : 0
% 2.56/1.35  #Sup     : 77
% 2.56/1.35  #Fact    : 0
% 2.56/1.35  #Define  : 0
% 2.56/1.35  #Split   : 0
% 2.56/1.35  #Chain   : 0
% 2.56/1.35  #Close   : 0
% 2.56/1.35  
% 2.56/1.35  Ordering : KBO
% 2.56/1.35  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 0
% 2.56/1.35  #Demod        : 13
% 2.56/1.35  #Tautology    : 54
% 2.56/1.35  #SimpNegUnit  : 1
% 2.56/1.35  #BackRed      : 0
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.35  Preprocessing        : 0.33
% 2.56/1.35  Parsing              : 0.17
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.24
% 2.56/1.35  Inferencing          : 0.10
% 2.56/1.35  Reduction            : 0.07
% 2.56/1.35  Demodulation         : 0.05
% 2.56/1.35  BG Simplification    : 0.02
% 2.56/1.35  Subsumption          : 0.04
% 2.56/1.35  Abstraction          : 0.02
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
