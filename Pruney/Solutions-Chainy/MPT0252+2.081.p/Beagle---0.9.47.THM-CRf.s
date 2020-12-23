%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 104 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :   79 ( 125 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [B_78,C_79,A_80] :
      ( r2_hidden(B_78,C_79)
      | ~ r1_tarski(k2_tarski(A_80,B_78),C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_117,plain,(
    ! [B_78,A_80] : r2_hidden(B_78,k2_tarski(A_80,B_78)) ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_88,plain,(
    ! [A_70,C_71,B_72] :
      ( r2_hidden(A_70,C_71)
      | ~ r1_tarski(k2_tarski(A_70,B_72),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [A_70,B_72] : r2_hidden(A_70,k2_tarski(A_70,B_72)) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_18,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    ! [D_91,C_92,B_93,A_94] : k2_enumset1(D_91,C_92,B_93,A_94) = k2_enumset1(A_94,B_93,C_92,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [D_91,C_92,B_93] : k2_enumset1(D_91,C_92,B_93,B_93) = k1_enumset1(B_93,C_92,D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_20])).

tff(c_22,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : k5_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47) = k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : k6_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53,G_54) = k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_320,plain,(
    ! [G_129,H_135,E_132,C_128,A_133,F_134,D_131,B_130] : k2_xboole_0(k4_enumset1(A_133,B_130,C_128,D_131,E_132,F_134),k2_tarski(G_129,H_135)) = k6_enumset1(A_133,B_130,C_128,D_131,E_132,F_134,G_129,H_135) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_340,plain,(
    ! [E_138,B_136,A_139,C_141,H_137,F_143,G_142,D_140] : r1_tarski(k4_enumset1(A_139,B_136,C_141,D_140,E_138,F_143),k6_enumset1(A_139,B_136,C_141,D_140,E_138,F_143,G_142,H_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_10])).

tff(c_345,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : r1_tarski(k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52),k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_352,plain,(
    ! [C_148,E_149,G_150,D_145,B_146,F_144,A_147] : r1_tarski(k3_enumset1(A_147,B_146,C_148,D_145,E_149),k5_enumset1(A_147,B_146,C_148,D_145,E_149,F_144,G_150)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_345])).

tff(c_357,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : r1_tarski(k3_enumset1(A_42,A_42,B_43,C_44,D_45),k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_352])).

tff(c_364,plain,(
    ! [E_151,A_154,F_155,C_156,B_153,D_152] : r1_tarski(k2_enumset1(A_154,B_153,C_156,D_152),k4_enumset1(A_154,B_153,C_156,D_152,E_151,F_155)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_357])).

tff(c_369,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : r1_tarski(k2_enumset1(A_37,A_37,B_38,C_39),k3_enumset1(A_37,B_38,C_39,D_40,E_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_364])).

tff(c_405,plain,(
    ! [C_170,D_168,A_166,B_167,E_169] : r1_tarski(k1_enumset1(A_166,B_167,C_170),k3_enumset1(A_166,B_167,C_170,D_168,E_169)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_369])).

tff(c_416,plain,(
    ! [A_33,B_34,C_35,D_36] : r1_tarski(k1_enumset1(A_33,A_33,B_34),k2_enumset1(A_33,B_34,C_35,D_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_405])).

tff(c_423,plain,(
    ! [A_171,B_172,C_173,D_174] : r1_tarski(k2_tarski(A_171,B_172),k2_enumset1(A_171,B_172,C_173,D_174)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_416])).

tff(c_613,plain,(
    ! [D_212,C_213,B_214] : r1_tarski(k2_tarski(D_212,C_213),k1_enumset1(B_214,C_213,D_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_423])).

tff(c_638,plain,(
    ! [B_215,A_216] : r1_tarski(k2_tarski(B_215,A_216),k2_tarski(A_216,B_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_613])).

tff(c_266,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(k2_tarski(A_104,B_105),C_106)
      | ~ r2_hidden(B_105,C_106)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_tarski(A_104,B_105) = C_106
      | ~ r1_tarski(C_106,k2_tarski(A_104,B_105))
      | ~ r2_hidden(B_105,C_106)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(resolution,[status(thm)],[c_266,c_4])).

tff(c_641,plain,(
    ! [B_215,A_216] :
      ( k2_tarski(B_215,A_216) = k2_tarski(A_216,B_215)
      | ~ r2_hidden(B_215,k2_tarski(B_215,A_216))
      | ~ r2_hidden(A_216,k2_tarski(B_215,A_216)) ) ),
    inference(resolution,[status(thm)],[c_638,c_277])).

tff(c_660,plain,(
    ! [B_217,A_218] : k2_tarski(B_217,A_218) = k2_tarski(A_218,B_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_98,c_641])).

tff(c_30,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_814,plain,(
    ! [A_228,B_229] : k3_tarski(k2_tarski(A_228,B_229)) = k2_xboole_0(B_229,A_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_30])).

tff(c_820,plain,(
    ! [B_229,A_228] : k2_xboole_0(B_229,A_228) = k2_xboole_0(A_228,B_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_30])).

tff(c_40,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_837,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_99])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_837])).

tff(c_842,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_849,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_10])).

tff(c_36,plain,(
    ! [A_57,C_59,B_58] :
      ( r2_hidden(A_57,C_59)
      | ~ r1_tarski(k2_tarski(A_57,B_58),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_856,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_849,c_36])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.40  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.84/1.40  
% 2.84/1.40  %Foreground sorts:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Background operators:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Foreground operators:
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  
% 2.84/1.42  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.84/1.42  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.84/1.42  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.42  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.84/1.42  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.42  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 2.84/1.42  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.84/1.42  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.84/1.42  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.84/1.42  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.84/1.42  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.84/1.42  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 2.84/1.42  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.84/1.42  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.42  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.42  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.42  tff(c_107, plain, (![B_78, C_79, A_80]: (r2_hidden(B_78, C_79) | ~r1_tarski(k2_tarski(A_80, B_78), C_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.42  tff(c_117, plain, (![B_78, A_80]: (r2_hidden(B_78, k2_tarski(A_80, B_78)))), inference(resolution, [status(thm)], [c_8, c_107])).
% 2.84/1.42  tff(c_88, plain, (![A_70, C_71, B_72]: (r2_hidden(A_70, C_71) | ~r1_tarski(k2_tarski(A_70, B_72), C_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.42  tff(c_98, plain, (![A_70, B_72]: (r2_hidden(A_70, k2_tarski(A_70, B_72)))), inference(resolution, [status(thm)], [c_8, c_88])).
% 2.84/1.42  tff(c_18, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.42  tff(c_140, plain, (![D_91, C_92, B_93, A_94]: (k2_enumset1(D_91, C_92, B_93, A_94)=k2_enumset1(A_94, B_93, C_92, D_91))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.42  tff(c_20, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.42  tff(c_156, plain, (![D_91, C_92, B_93]: (k2_enumset1(D_91, C_92, B_93, B_93)=k1_enumset1(B_93, C_92, D_91))), inference(superposition, [status(thm), theory('equality')], [c_140, c_20])).
% 2.84/1.42  tff(c_22, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.42  tff(c_24, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.42  tff(c_26, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (k5_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47)=k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.42  tff(c_28, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (k6_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53, G_54)=k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.42  tff(c_320, plain, (![G_129, H_135, E_132, C_128, A_133, F_134, D_131, B_130]: (k2_xboole_0(k4_enumset1(A_133, B_130, C_128, D_131, E_132, F_134), k2_tarski(G_129, H_135))=k6_enumset1(A_133, B_130, C_128, D_131, E_132, F_134, G_129, H_135))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.42  tff(c_340, plain, (![E_138, B_136, A_139, C_141, H_137, F_143, G_142, D_140]: (r1_tarski(k4_enumset1(A_139, B_136, C_141, D_140, E_138, F_143), k6_enumset1(A_139, B_136, C_141, D_140, E_138, F_143, G_142, H_137)))), inference(superposition, [status(thm), theory('equality')], [c_320, c_10])).
% 2.84/1.42  tff(c_345, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (r1_tarski(k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52), k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_340])).
% 2.84/1.42  tff(c_352, plain, (![C_148, E_149, G_150, D_145, B_146, F_144, A_147]: (r1_tarski(k3_enumset1(A_147, B_146, C_148, D_145, E_149), k5_enumset1(A_147, B_146, C_148, D_145, E_149, F_144, G_150)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_345])).
% 2.84/1.42  tff(c_357, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (r1_tarski(k3_enumset1(A_42, A_42, B_43, C_44, D_45), k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_352])).
% 2.84/1.42  tff(c_364, plain, (![E_151, A_154, F_155, C_156, B_153, D_152]: (r1_tarski(k2_enumset1(A_154, B_153, C_156, D_152), k4_enumset1(A_154, B_153, C_156, D_152, E_151, F_155)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_357])).
% 2.84/1.42  tff(c_369, plain, (![C_39, B_38, A_37, D_40, E_41]: (r1_tarski(k2_enumset1(A_37, A_37, B_38, C_39), k3_enumset1(A_37, B_38, C_39, D_40, E_41)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_364])).
% 2.84/1.42  tff(c_405, plain, (![C_170, D_168, A_166, B_167, E_169]: (r1_tarski(k1_enumset1(A_166, B_167, C_170), k3_enumset1(A_166, B_167, C_170, D_168, E_169)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_369])).
% 2.84/1.42  tff(c_416, plain, (![A_33, B_34, C_35, D_36]: (r1_tarski(k1_enumset1(A_33, A_33, B_34), k2_enumset1(A_33, B_34, C_35, D_36)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_405])).
% 2.84/1.42  tff(c_423, plain, (![A_171, B_172, C_173, D_174]: (r1_tarski(k2_tarski(A_171, B_172), k2_enumset1(A_171, B_172, C_173, D_174)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_416])).
% 2.84/1.42  tff(c_613, plain, (![D_212, C_213, B_214]: (r1_tarski(k2_tarski(D_212, C_213), k1_enumset1(B_214, C_213, D_212)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_423])).
% 2.84/1.42  tff(c_638, plain, (![B_215, A_216]: (r1_tarski(k2_tarski(B_215, A_216), k2_tarski(A_216, B_215)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_613])).
% 2.84/1.42  tff(c_266, plain, (![A_104, B_105, C_106]: (r1_tarski(k2_tarski(A_104, B_105), C_106) | ~r2_hidden(B_105, C_106) | ~r2_hidden(A_104, C_106))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.42  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.42  tff(c_277, plain, (![A_104, B_105, C_106]: (k2_tarski(A_104, B_105)=C_106 | ~r1_tarski(C_106, k2_tarski(A_104, B_105)) | ~r2_hidden(B_105, C_106) | ~r2_hidden(A_104, C_106))), inference(resolution, [status(thm)], [c_266, c_4])).
% 2.84/1.42  tff(c_641, plain, (![B_215, A_216]: (k2_tarski(B_215, A_216)=k2_tarski(A_216, B_215) | ~r2_hidden(B_215, k2_tarski(B_215, A_216)) | ~r2_hidden(A_216, k2_tarski(B_215, A_216)))), inference(resolution, [status(thm)], [c_638, c_277])).
% 2.84/1.42  tff(c_660, plain, (![B_217, A_218]: (k2_tarski(B_217, A_218)=k2_tarski(A_218, B_217))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_98, c_641])).
% 2.84/1.42  tff(c_30, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.42  tff(c_814, plain, (![A_228, B_229]: (k3_tarski(k2_tarski(A_228, B_229))=k2_xboole_0(B_229, A_228))), inference(superposition, [status(thm), theory('equality')], [c_660, c_30])).
% 2.84/1.42  tff(c_820, plain, (![B_229, A_228]: (k2_xboole_0(B_229, A_228)=k2_xboole_0(A_228, B_229))), inference(superposition, [status(thm), theory('equality')], [c_814, c_30])).
% 2.84/1.42  tff(c_40, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.42  tff(c_75, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.42  tff(c_82, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.84/1.42  tff(c_99, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_82])).
% 2.84/1.42  tff(c_837, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_820, c_99])).
% 2.84/1.42  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_837])).
% 2.84/1.42  tff(c_842, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_82])).
% 2.84/1.42  tff(c_849, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_842, c_10])).
% 2.84/1.42  tff(c_36, plain, (![A_57, C_59, B_58]: (r2_hidden(A_57, C_59) | ~r1_tarski(k2_tarski(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.42  tff(c_856, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_849, c_36])).
% 2.84/1.42  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_856])).
% 2.84/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  Inference rules
% 2.84/1.42  ----------------------
% 2.84/1.42  #Ref     : 0
% 2.84/1.42  #Sup     : 199
% 2.84/1.42  #Fact    : 0
% 2.84/1.42  #Define  : 0
% 2.84/1.42  #Split   : 1
% 2.84/1.42  #Chain   : 0
% 2.84/1.42  #Close   : 0
% 2.84/1.42  
% 2.84/1.42  Ordering : KBO
% 2.84/1.42  
% 2.84/1.42  Simplification rules
% 2.84/1.42  ----------------------
% 2.84/1.42  #Subsume      : 8
% 2.84/1.42  #Demod        : 84
% 2.84/1.42  #Tautology    : 114
% 2.84/1.42  #SimpNegUnit  : 1
% 2.84/1.42  #BackRed      : 3
% 2.84/1.42  
% 2.84/1.42  #Partial instantiations: 0
% 2.84/1.42  #Strategies tried      : 1
% 2.84/1.42  
% 2.84/1.42  Timing (in seconds)
% 2.84/1.42  ----------------------
% 2.84/1.42  Preprocessing        : 0.31
% 2.84/1.42  Parsing              : 0.16
% 2.84/1.42  CNF conversion       : 0.02
% 2.84/1.42  Main loop            : 0.35
% 2.84/1.42  Inferencing          : 0.13
% 2.84/1.42  Reduction            : 0.12
% 2.84/1.42  Demodulation         : 0.09
% 2.84/1.42  BG Simplification    : 0.02
% 2.84/1.42  Subsumption          : 0.06
% 2.84/1.42  Abstraction          : 0.02
% 2.84/1.42  MUC search           : 0.00
% 2.84/1.42  Cooper               : 0.00
% 2.84/1.42  Total                : 0.69
% 2.84/1.42  Index Insertion      : 0.00
% 2.84/1.42  Index Deletion       : 0.00
% 2.84/1.42  Index Matching       : 0.00
% 2.84/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
