%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 129 expanded)
%              Number of equality atoms :   64 (  93 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] : k5_enumset1(A_49,A_49,B_50,C_51,D_52,E_53,F_54) = k4_enumset1(A_49,B_50,C_51,D_52,E_53,F_54) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_919,plain,(
    ! [B_166,E_165,C_163,G_167,F_162,A_168,D_164] : k2_xboole_0(k4_enumset1(A_168,B_166,C_163,D_164,E_165,F_162),k1_tarski(G_167)) = k5_enumset1(A_168,B_166,C_163,D_164,E_165,F_162,G_167) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_928,plain,(
    ! [C_46,E_48,G_167,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,G_167) = k2_xboole_0(k3_enumset1(A_44,B_45,C_46,D_47,E_48),k1_tarski(G_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_919])).

tff(c_979,plain,(
    ! [D_172,A_176,C_173,B_175,E_171,G_174] : k2_xboole_0(k3_enumset1(A_176,B_175,C_173,D_172,E_171),k1_tarski(G_174)) = k4_enumset1(A_176,B_175,C_173,D_172,E_171,G_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_928])).

tff(c_988,plain,(
    ! [C_42,A_40,D_43,G_174,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,G_174) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(G_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_979])).

tff(c_992,plain,(
    ! [A_177,D_178,G_180,C_179,B_181] : k2_xboole_0(k2_enumset1(A_177,B_181,C_179,D_178),k1_tarski(G_180)) = k3_enumset1(A_177,B_181,C_179,D_178,G_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988])).

tff(c_1001,plain,(
    ! [A_37,B_38,C_39,G_180] : k3_enumset1(A_37,A_37,B_38,C_39,G_180) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(G_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_1005,plain,(
    ! [A_182,B_183,C_184,G_185] : k2_xboole_0(k1_enumset1(A_182,B_183,C_184),k1_tarski(G_185)) = k2_enumset1(A_182,B_183,C_184,G_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1001])).

tff(c_1014,plain,(
    ! [A_35,B_36,G_185] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(G_185)) = k2_enumset1(A_35,A_35,B_36,G_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1005])).

tff(c_1019,plain,(
    ! [A_190,B_191,G_192] : k2_xboole_0(k2_tarski(A_190,B_191),k1_tarski(G_192)) = k1_enumset1(A_190,B_191,G_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1014])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_133,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_91,B_92] :
      ( ~ r1_xboole_0(A_91,B_92)
      | k3_xboole_0(A_91,B_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_165,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_292,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_309,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_292])).

tff(c_318,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_309])).

tff(c_219,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_237,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_219])).

tff(c_240,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_237])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_319,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_315])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_123,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_312,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_292])).

tff(c_399,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_312])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_406,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_20])).

tff(c_410,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_406])).

tff(c_1025,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_410])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1053,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_24])).

tff(c_538,plain,(
    ! [E_121,C_122,B_123,A_124] :
      ( E_121 = C_122
      | E_121 = B_123
      | E_121 = A_124
      | ~ r2_hidden(E_121,k1_enumset1(A_124,B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_545,plain,(
    ! [E_121,B_36,A_35] :
      ( E_121 = B_36
      | E_121 = A_35
      | E_121 = A_35
      | ~ r2_hidden(E_121,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_538])).

tff(c_1062,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1053,c_545])).

tff(c_1066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_1062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.00/1.45  
% 3.00/1.45  %Foreground sorts:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Background operators:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Foreground operators:
% 3.00/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.00/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.45  
% 3.27/1.47  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.27/1.47  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.47  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.47  tff(f_88, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.27/1.47  tff(f_90, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.27/1.47  tff(f_92, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.27/1.47  tff(f_80, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 3.27/1.47  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.27/1.47  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.27/1.47  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.27/1.47  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.27/1.47  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.27/1.47  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.27/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.27/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.27/1.47  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.27/1.47  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.27/1.47  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.27/1.47  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.27/1.47  tff(c_52, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.27/1.47  tff(c_50, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.47  tff(c_54, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.27/1.47  tff(c_56, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.27/1.47  tff(c_58, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (k5_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54)=k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.47  tff(c_919, plain, (![B_166, E_165, C_163, G_167, F_162, A_168, D_164]: (k2_xboole_0(k4_enumset1(A_168, B_166, C_163, D_164, E_165, F_162), k1_tarski(G_167))=k5_enumset1(A_168, B_166, C_163, D_164, E_165, F_162, G_167))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.47  tff(c_928, plain, (![C_46, E_48, G_167, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, G_167)=k2_xboole_0(k3_enumset1(A_44, B_45, C_46, D_47, E_48), k1_tarski(G_167)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_919])).
% 3.27/1.47  tff(c_979, plain, (![D_172, A_176, C_173, B_175, E_171, G_174]: (k2_xboole_0(k3_enumset1(A_176, B_175, C_173, D_172, E_171), k1_tarski(G_174))=k4_enumset1(A_176, B_175, C_173, D_172, E_171, G_174))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_928])).
% 3.27/1.47  tff(c_988, plain, (![C_42, A_40, D_43, G_174, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, G_174)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(G_174)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_979])).
% 3.27/1.47  tff(c_992, plain, (![A_177, D_178, G_180, C_179, B_181]: (k2_xboole_0(k2_enumset1(A_177, B_181, C_179, D_178), k1_tarski(G_180))=k3_enumset1(A_177, B_181, C_179, D_178, G_180))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988])).
% 3.27/1.47  tff(c_1001, plain, (![A_37, B_38, C_39, G_180]: (k3_enumset1(A_37, A_37, B_38, C_39, G_180)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(G_180)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 3.27/1.47  tff(c_1005, plain, (![A_182, B_183, C_184, G_185]: (k2_xboole_0(k1_enumset1(A_182, B_183, C_184), k1_tarski(G_185))=k2_enumset1(A_182, B_183, C_184, G_185))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1001])).
% 3.27/1.47  tff(c_1014, plain, (![A_35, B_36, G_185]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(G_185))=k2_enumset1(A_35, A_35, B_36, G_185))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1005])).
% 3.27/1.47  tff(c_1019, plain, (![A_190, B_191, G_192]: (k2_xboole_0(k2_tarski(A_190, B_191), k1_tarski(G_192))=k1_enumset1(A_190, B_191, G_192))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1014])).
% 3.27/1.47  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.47  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.47  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.47  tff(c_133, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.47  tff(c_161, plain, (![A_91, B_92]: (~r1_xboole_0(A_91, B_92) | k3_xboole_0(A_91, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 3.27/1.47  tff(c_165, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 3.27/1.47  tff(c_292, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.27/1.47  tff(c_309, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_292])).
% 3.27/1.47  tff(c_318, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_309])).
% 3.27/1.47  tff(c_219, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.47  tff(c_237, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_219])).
% 3.27/1.47  tff(c_240, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_237])).
% 3.27/1.47  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.47  tff(c_315, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 3.27/1.47  tff(c_319, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_315])).
% 3.27/1.47  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.27/1.47  tff(c_123, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.47  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_123])).
% 3.27/1.47  tff(c_312, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_292])).
% 3.27/1.47  tff(c_399, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_319, c_312])).
% 3.27/1.47  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.47  tff(c_406, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_399, c_20])).
% 3.27/1.47  tff(c_410, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_406])).
% 3.27/1.47  tff(c_1025, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_410])).
% 3.27/1.47  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.47  tff(c_1053, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_24])).
% 3.27/1.47  tff(c_538, plain, (![E_121, C_122, B_123, A_124]: (E_121=C_122 | E_121=B_123 | E_121=A_124 | ~r2_hidden(E_121, k1_enumset1(A_124, B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.47  tff(c_545, plain, (![E_121, B_36, A_35]: (E_121=B_36 | E_121=A_35 | E_121=A_35 | ~r2_hidden(E_121, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_538])).
% 3.27/1.47  tff(c_1062, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1053, c_545])).
% 3.27/1.47  tff(c_1066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_1062])).
% 3.27/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.47  
% 3.27/1.47  Inference rules
% 3.27/1.47  ----------------------
% 3.27/1.47  #Ref     : 0
% 3.27/1.47  #Sup     : 234
% 3.27/1.47  #Fact    : 2
% 3.27/1.47  #Define  : 0
% 3.27/1.47  #Split   : 1
% 3.27/1.47  #Chain   : 0
% 3.27/1.47  #Close   : 0
% 3.27/1.47  
% 3.27/1.47  Ordering : KBO
% 3.27/1.47  
% 3.27/1.47  Simplification rules
% 3.27/1.47  ----------------------
% 3.27/1.47  #Subsume      : 15
% 3.27/1.47  #Demod        : 168
% 3.27/1.47  #Tautology    : 163
% 3.27/1.47  #SimpNegUnit  : 4
% 3.27/1.47  #BackRed      : 2
% 3.27/1.47  
% 3.27/1.47  #Partial instantiations: 0
% 3.27/1.47  #Strategies tried      : 1
% 3.27/1.47  
% 3.27/1.47  Timing (in seconds)
% 3.27/1.47  ----------------------
% 3.27/1.47  Preprocessing        : 0.33
% 3.27/1.47  Parsing              : 0.16
% 3.27/1.47  CNF conversion       : 0.03
% 3.27/1.47  Main loop            : 0.38
% 3.27/1.47  Inferencing          : 0.14
% 3.27/1.47  Reduction            : 0.13
% 3.27/1.47  Demodulation         : 0.10
% 3.27/1.47  BG Simplification    : 0.02
% 3.27/1.47  Subsumption          : 0.06
% 3.27/1.47  Abstraction          : 0.02
% 3.27/1.47  MUC search           : 0.00
% 3.27/1.47  Cooper               : 0.00
% 3.27/1.47  Total                : 0.75
% 3.27/1.48  Index Insertion      : 0.00
% 3.27/1.48  Index Deletion       : 0.00
% 3.27/1.48  Index Matching       : 0.00
% 3.27/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
