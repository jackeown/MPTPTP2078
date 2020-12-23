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
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   15
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

tff(c_999,plain,(
    ! [A_171,C_166,D_167,E_168,F_165,G_170,B_169] : k2_xboole_0(k4_enumset1(A_171,B_169,C_166,D_167,E_168,F_165),k1_tarski(G_170)) = k5_enumset1(A_171,B_169,C_166,D_167,E_168,F_165,G_170) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1008,plain,(
    ! [C_46,E_48,A_44,G_170,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,G_170) = k2_xboole_0(k3_enumset1(A_44,B_45,C_46,D_47,E_48),k1_tarski(G_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_999])).

tff(c_1012,plain,(
    ! [D_173,A_176,G_177,B_175,C_174,E_172] : k2_xboole_0(k3_enumset1(A_176,B_175,C_174,D_173,E_172),k1_tarski(G_177)) = k4_enumset1(A_176,B_175,C_174,D_173,E_172,G_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1008])).

tff(c_1021,plain,(
    ! [C_42,G_177,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,G_177) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(G_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1012])).

tff(c_1025,plain,(
    ! [A_178,D_179,C_180,B_182,G_181] : k2_xboole_0(k2_enumset1(A_178,B_182,C_180,D_179),k1_tarski(G_181)) = k3_enumset1(A_178,B_182,C_180,D_179,G_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1021])).

tff(c_1034,plain,(
    ! [A_37,B_38,C_39,G_181] : k3_enumset1(A_37,A_37,B_38,C_39,G_181) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(G_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1025])).

tff(c_1039,plain,(
    ! [A_187,B_188,C_189,G_190] : k2_xboole_0(k1_enumset1(A_187,B_188,C_189),k1_tarski(G_190)) = k2_enumset1(A_187,B_188,C_189,G_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1034])).

tff(c_1048,plain,(
    ! [A_35,B_36,G_190] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(G_190)) = k2_enumset1(A_35,A_35,B_36,G_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1039])).

tff(c_1052,plain,(
    ! [A_191,B_192,G_193] : k2_xboole_0(k2_tarski(A_191,B_192),k1_tarski(G_193)) = k1_enumset1(A_191,B_192,G_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1048])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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

tff(c_215,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_224,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_215])).

tff(c_234,plain,(
    ! [A_100] : k4_xboole_0(A_100,k1_xboole_0) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_224])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_240,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k3_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_248,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_240])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_285,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_230])).

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

tff(c_227,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_215])).

tff(c_408,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_227])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_415,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_20])).

tff(c_419,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_415])).

tff(c_1058,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_419])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1086,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_24])).

tff(c_497,plain,(
    ! [E_120,C_121,B_122,A_123] :
      ( E_120 = C_121
      | E_120 = B_122
      | E_120 = A_123
      | ~ r2_hidden(E_120,k1_enumset1(A_123,B_122,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_504,plain,(
    ! [E_120,B_36,A_35] :
      ( E_120 = B_36
      | E_120 = A_35
      | E_120 = A_35
      | ~ r2_hidden(E_120,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_497])).

tff(c_1095,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1086,c_504])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_1095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.20/1.49  
% 3.20/1.49  %Foreground sorts:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Background operators:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Foreground operators:
% 3.20/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.20/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.20/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.49  
% 3.20/1.50  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.20/1.50  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.20/1.50  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.20/1.50  tff(f_88, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.20/1.50  tff(f_90, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.20/1.50  tff(f_92, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.20/1.50  tff(f_80, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 3.20/1.51  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.51  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.20/1.51  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.51  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.20/1.51  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.51  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.51  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.51  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.20/1.51  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.20/1.51  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.51  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.51  tff(c_52, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.51  tff(c_50, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.51  tff(c_54, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.51  tff(c_56, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.51  tff(c_58, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (k5_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54)=k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.51  tff(c_999, plain, (![A_171, C_166, D_167, E_168, F_165, G_170, B_169]: (k2_xboole_0(k4_enumset1(A_171, B_169, C_166, D_167, E_168, F_165), k1_tarski(G_170))=k5_enumset1(A_171, B_169, C_166, D_167, E_168, F_165, G_170))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.51  tff(c_1008, plain, (![C_46, E_48, A_44, G_170, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, G_170)=k2_xboole_0(k3_enumset1(A_44, B_45, C_46, D_47, E_48), k1_tarski(G_170)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_999])).
% 3.20/1.51  tff(c_1012, plain, (![D_173, A_176, G_177, B_175, C_174, E_172]: (k2_xboole_0(k3_enumset1(A_176, B_175, C_174, D_173, E_172), k1_tarski(G_177))=k4_enumset1(A_176, B_175, C_174, D_173, E_172, G_177))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1008])).
% 3.20/1.51  tff(c_1021, plain, (![C_42, G_177, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, G_177)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(G_177)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1012])).
% 3.20/1.51  tff(c_1025, plain, (![A_178, D_179, C_180, B_182, G_181]: (k2_xboole_0(k2_enumset1(A_178, B_182, C_180, D_179), k1_tarski(G_181))=k3_enumset1(A_178, B_182, C_180, D_179, G_181))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1021])).
% 3.20/1.51  tff(c_1034, plain, (![A_37, B_38, C_39, G_181]: (k3_enumset1(A_37, A_37, B_38, C_39, G_181)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(G_181)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1025])).
% 3.20/1.51  tff(c_1039, plain, (![A_187, B_188, C_189, G_190]: (k2_xboole_0(k1_enumset1(A_187, B_188, C_189), k1_tarski(G_190))=k2_enumset1(A_187, B_188, C_189, G_190))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1034])).
% 3.20/1.51  tff(c_1048, plain, (![A_35, B_36, G_190]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(G_190))=k2_enumset1(A_35, A_35, B_36, G_190))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1039])).
% 3.20/1.51  tff(c_1052, plain, (![A_191, B_192, G_193]: (k2_xboole_0(k2_tarski(A_191, B_192), k1_tarski(G_193))=k1_enumset1(A_191, B_192, G_193))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1048])).
% 3.20/1.51  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.51  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.20/1.51  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.51  tff(c_133, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.51  tff(c_161, plain, (![A_91, B_92]: (~r1_xboole_0(A_91, B_92) | k3_xboole_0(A_91, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 3.20/1.51  tff(c_165, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 3.20/1.51  tff(c_215, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.51  tff(c_224, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_215])).
% 3.20/1.51  tff(c_234, plain, (![A_100]: (k4_xboole_0(A_100, k1_xboole_0)=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_224])).
% 3.20/1.51  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.51  tff(c_240, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k3_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 3.20/1.51  tff(c_248, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_240])).
% 3.20/1.51  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.51  tff(c_230, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 3.20/1.51  tff(c_285, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_230])).
% 3.20/1.51  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.51  tff(c_123, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.51  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_123])).
% 3.20/1.51  tff(c_227, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_215])).
% 3.20/1.51  tff(c_408, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_285, c_227])).
% 3.20/1.51  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.51  tff(c_415, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_408, c_20])).
% 3.20/1.51  tff(c_419, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_415])).
% 3.20/1.51  tff(c_1058, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_419])).
% 3.20/1.51  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.20/1.51  tff(c_1086, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1058, c_24])).
% 3.20/1.51  tff(c_497, plain, (![E_120, C_121, B_122, A_123]: (E_120=C_121 | E_120=B_122 | E_120=A_123 | ~r2_hidden(E_120, k1_enumset1(A_123, B_122, C_121)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.20/1.51  tff(c_504, plain, (![E_120, B_36, A_35]: (E_120=B_36 | E_120=A_35 | E_120=A_35 | ~r2_hidden(E_120, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_497])).
% 3.20/1.51  tff(c_1095, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1086, c_504])).
% 3.20/1.51  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_1095])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 0
% 3.20/1.51  #Sup     : 244
% 3.20/1.51  #Fact    : 2
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 1
% 3.20/1.51  #Chain   : 0
% 3.20/1.51  #Close   : 0
% 3.20/1.51  
% 3.20/1.51  Ordering : KBO
% 3.20/1.51  
% 3.20/1.51  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 15
% 3.20/1.51  #Demod        : 194
% 3.20/1.51  #Tautology    : 163
% 3.20/1.51  #SimpNegUnit  : 4
% 3.20/1.51  #BackRed      : 1
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 0
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.51  Preprocessing        : 0.35
% 3.20/1.51  Parsing              : 0.18
% 3.20/1.51  CNF conversion       : 0.02
% 3.20/1.51  Main loop            : 0.38
% 3.20/1.51  Inferencing          : 0.14
% 3.20/1.51  Reduction            : 0.14
% 3.20/1.51  Demodulation         : 0.10
% 3.20/1.51  BG Simplification    : 0.02
% 3.20/1.51  Subsumption          : 0.06
% 3.20/1.51  Abstraction          : 0.02
% 3.20/1.51  MUC search           : 0.00
% 3.20/1.51  Cooper               : 0.00
% 3.20/1.51  Total                : 0.76
% 3.20/1.51  Index Insertion      : 0.00
% 3.20/1.51  Index Deletion       : 0.00
% 3.20/1.51  Index Matching       : 0.00
% 3.20/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
