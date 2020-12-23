%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 34.50s
% Output     : CNFRefutation 34.63s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 105 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   44 (  81 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_228,plain,(
    ! [A_92,B_93,C_94] : k2_zfmisc_1(k2_tarski(A_92,B_93),k1_tarski(C_94)) = k2_tarski(k4_tarski(A_92,C_94),k4_tarski(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_63,B_64,C_65] : k2_zfmisc_1(k2_zfmisc_1(A_63,B_64),C_65) = k3_zfmisc_1(A_63,B_64,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_240,plain,(
    ! [A_92,C_94,B_93,C_65] : k2_zfmisc_1(k2_tarski(k4_tarski(A_92,C_94),k4_tarski(B_93,C_94)),C_65) = k3_zfmisc_1(k2_tarski(A_92,B_93),k1_tarski(C_94),C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_34])).

tff(c_32,plain,(
    ! [A_60,B_61,C_62] : k4_tarski(k4_tarski(A_60,B_61),C_62) = k3_mcart_1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1067,plain,(
    ! [A_170,C_171,D_172,B_173] : k2_enumset1(k4_tarski(A_170,C_171),k4_tarski(A_170,D_172),k4_tarski(B_173,C_171),k4_tarski(B_173,D_172)) = k2_zfmisc_1(k2_tarski(A_170,B_173),k2_tarski(C_171,D_172)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1086,plain,(
    ! [A_170,A_60,D_172,C_62,B_61] : k2_enumset1(k4_tarski(A_170,C_62),k4_tarski(A_170,D_172),k3_mcart_1(A_60,B_61,C_62),k4_tarski(k4_tarski(A_60,B_61),D_172)) = k2_zfmisc_1(k2_tarski(A_170,k4_tarski(A_60,B_61)),k2_tarski(C_62,D_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1067])).

tff(c_3365,plain,(
    ! [A_342,B_341,D_339,C_340,A_338] : k2_enumset1(k4_tarski(A_338,C_340),k4_tarski(A_338,D_339),k3_mcart_1(A_342,B_341,C_340),k3_mcart_1(A_342,B_341,D_339)) = k2_zfmisc_1(k2_tarski(A_338,k4_tarski(A_342,B_341)),k2_tarski(C_340,D_339)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1086])).

tff(c_3402,plain,(
    ! [A_342,B_341,A_60,D_339,C_62,B_61] : k2_enumset1(k3_mcart_1(A_60,B_61,C_62),k4_tarski(k4_tarski(A_60,B_61),D_339),k3_mcart_1(A_342,B_341,C_62),k3_mcart_1(A_342,B_341,D_339)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_60,B_61),k4_tarski(A_342,B_341)),k2_tarski(C_62,D_339)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3365])).

tff(c_3415,plain,(
    ! [A_342,B_341,A_60,D_339,C_62,B_61] : k2_enumset1(k3_mcart_1(A_60,B_61,C_62),k3_mcart_1(A_60,B_61,D_339),k3_mcart_1(A_342,B_341,C_62),k3_mcart_1(A_342,B_341,D_339)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_60,B_61),k4_tarski(A_342,B_341)),k2_tarski(C_62,D_339)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3402])).

tff(c_22,plain,(
    ! [A_48,C_50,B_49] : k1_enumset1(A_48,C_50,B_49) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,G_47,E_45] : k6_enumset1(A_41,A_41,B_42,C_43,D_44,E_45,F_46,G_47) = k5_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_865,plain,(
    ! [C_158,G_151,E_155,H_153,B_152,A_154,F_157,D_156] : k2_xboole_0(k5_enumset1(A_154,B_152,C_158,D_156,E_155,F_157,G_151),k1_tarski(H_153)) = k6_enumset1(A_154,B_152,C_158,D_156,E_155,F_157,G_151,H_153) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_874,plain,(
    ! [A_35,F_40,B_36,H_153,C_37,D_38,E_39] : k6_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40,H_153) = k2_xboole_0(k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40),k1_tarski(H_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_865])).

tff(c_1488,plain,(
    ! [B_211,D_210,A_205,E_209,F_207,H_206,C_208] : k2_xboole_0(k4_enumset1(A_205,B_211,C_208,D_210,E_209,F_207),k1_tarski(H_206)) = k5_enumset1(A_205,B_211,C_208,D_210,E_209,F_207,H_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_874])).

tff(c_1497,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,H_206] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,H_206) = k2_xboole_0(k3_enumset1(A_30,B_31,C_32,D_33,E_34),k1_tarski(H_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1488])).

tff(c_1501,plain,(
    ! [H_217,A_214,D_216,C_212,B_213,E_215] : k2_xboole_0(k3_enumset1(A_214,B_213,C_212,D_216,E_215),k1_tarski(H_217)) = k4_enumset1(A_214,B_213,C_212,D_216,E_215,H_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1497])).

tff(c_1510,plain,(
    ! [B_27,D_29,H_217,A_26,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,H_217) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(H_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1501])).

tff(c_1514,plain,(
    ! [B_219,C_222,A_220,H_221,D_218] : k2_xboole_0(k2_enumset1(A_220,B_219,C_222,D_218),k1_tarski(H_221)) = k3_enumset1(A_220,B_219,C_222,D_218,H_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1510])).

tff(c_1526,plain,(
    ! [A_23,B_24,C_25,H_221] : k3_enumset1(A_23,A_23,B_24,C_25,H_221) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(H_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1514])).

tff(c_1530,plain,(
    ! [A_223,B_224,C_225,H_226] : k2_xboole_0(k1_enumset1(A_223,B_224,C_225),k1_tarski(H_226)) = k2_enumset1(A_223,B_224,C_225,H_226) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1526])).

tff(c_1555,plain,(
    ! [A_227,C_228,B_229,H_230] : k2_xboole_0(k1_enumset1(A_227,C_228,B_229),k1_tarski(H_230)) = k2_enumset1(A_227,B_229,C_228,H_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1530])).

tff(c_1529,plain,(
    ! [A_23,B_24,C_25,H_221] : k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(H_221)) = k2_enumset1(A_23,B_24,C_25,H_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1526])).

tff(c_1561,plain,(
    ! [A_227,C_228,B_229,H_230] : k2_enumset1(A_227,C_228,B_229,H_230) = k2_enumset1(A_227,B_229,C_228,H_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_1529])).

tff(c_36,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1651,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_36])).

tff(c_63716,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_1651])).

tff(c_63719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_63716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.50/24.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.50/24.16  
% 34.50/24.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.50/24.17  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 34.50/24.17  
% 34.50/24.17  %Foreground sorts:
% 34.50/24.17  
% 34.50/24.17  
% 34.50/24.17  %Background operators:
% 34.50/24.17  
% 34.50/24.17  
% 34.50/24.17  %Foreground operators:
% 34.50/24.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.50/24.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 34.50/24.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 34.50/24.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 34.50/24.17  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 34.50/24.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 34.50/24.17  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 34.50/24.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 34.50/24.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 34.50/24.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.50/24.17  tff('#skF_5', type, '#skF_5': $i).
% 34.50/24.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 34.50/24.17  tff('#skF_2', type, '#skF_2': $i).
% 34.50/24.17  tff('#skF_3', type, '#skF_3': $i).
% 34.50/24.17  tff('#skF_1', type, '#skF_1': $i).
% 34.50/24.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 34.50/24.17  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 34.50/24.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 34.50/24.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.50/24.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 34.50/24.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.50/24.17  tff('#skF_4', type, '#skF_4': $i).
% 34.50/24.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.50/24.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.50/24.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 34.50/24.17  
% 34.63/24.18  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 34.63/24.18  tff(f_59, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 34.63/24.18  tff(f_57, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 34.63/24.18  tff(f_51, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 34.63/24.18  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 34.63/24.18  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 34.63/24.18  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 34.63/24.18  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 34.63/24.18  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 34.63/24.18  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 34.63/24.18  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 34.63/24.18  tff(f_62, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 34.63/24.18  tff(c_228, plain, (![A_92, B_93, C_94]: (k2_zfmisc_1(k2_tarski(A_92, B_93), k1_tarski(C_94))=k2_tarski(k4_tarski(A_92, C_94), k4_tarski(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 34.63/24.18  tff(c_34, plain, (![A_63, B_64, C_65]: (k2_zfmisc_1(k2_zfmisc_1(A_63, B_64), C_65)=k3_zfmisc_1(A_63, B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.63/24.18  tff(c_240, plain, (![A_92, C_94, B_93, C_65]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_92, C_94), k4_tarski(B_93, C_94)), C_65)=k3_zfmisc_1(k2_tarski(A_92, B_93), k1_tarski(C_94), C_65))), inference(superposition, [status(thm), theory('equality')], [c_228, c_34])).
% 34.63/24.18  tff(c_32, plain, (![A_60, B_61, C_62]: (k4_tarski(k4_tarski(A_60, B_61), C_62)=k3_mcart_1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 34.63/24.18  tff(c_1067, plain, (![A_170, C_171, D_172, B_173]: (k2_enumset1(k4_tarski(A_170, C_171), k4_tarski(A_170, D_172), k4_tarski(B_173, C_171), k4_tarski(B_173, D_172))=k2_zfmisc_1(k2_tarski(A_170, B_173), k2_tarski(C_171, D_172)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.63/24.18  tff(c_1086, plain, (![A_170, A_60, D_172, C_62, B_61]: (k2_enumset1(k4_tarski(A_170, C_62), k4_tarski(A_170, D_172), k3_mcart_1(A_60, B_61, C_62), k4_tarski(k4_tarski(A_60, B_61), D_172))=k2_zfmisc_1(k2_tarski(A_170, k4_tarski(A_60, B_61)), k2_tarski(C_62, D_172)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1067])).
% 34.63/24.18  tff(c_3365, plain, (![A_342, B_341, D_339, C_340, A_338]: (k2_enumset1(k4_tarski(A_338, C_340), k4_tarski(A_338, D_339), k3_mcart_1(A_342, B_341, C_340), k3_mcart_1(A_342, B_341, D_339))=k2_zfmisc_1(k2_tarski(A_338, k4_tarski(A_342, B_341)), k2_tarski(C_340, D_339)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1086])).
% 34.63/24.18  tff(c_3402, plain, (![A_342, B_341, A_60, D_339, C_62, B_61]: (k2_enumset1(k3_mcart_1(A_60, B_61, C_62), k4_tarski(k4_tarski(A_60, B_61), D_339), k3_mcart_1(A_342, B_341, C_62), k3_mcart_1(A_342, B_341, D_339))=k2_zfmisc_1(k2_tarski(k4_tarski(A_60, B_61), k4_tarski(A_342, B_341)), k2_tarski(C_62, D_339)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3365])).
% 34.63/24.18  tff(c_3415, plain, (![A_342, B_341, A_60, D_339, C_62, B_61]: (k2_enumset1(k3_mcart_1(A_60, B_61, C_62), k3_mcart_1(A_60, B_61, D_339), k3_mcart_1(A_342, B_341, C_62), k3_mcart_1(A_342, B_341, D_339))=k2_zfmisc_1(k2_tarski(k4_tarski(A_60, B_61), k4_tarski(A_342, B_341)), k2_tarski(C_62, D_339)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3402])).
% 34.63/24.18  tff(c_22, plain, (![A_48, C_50, B_49]: (k1_enumset1(A_48, C_50, B_49)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 34.63/24.18  tff(c_14, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.63/24.18  tff(c_12, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.63/24.18  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.63/24.18  tff(c_18, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40)=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.63/24.18  tff(c_20, plain, (![D_44, F_46, C_43, A_41, B_42, G_47, E_45]: (k6_enumset1(A_41, A_41, B_42, C_43, D_44, E_45, F_46, G_47)=k5_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 34.63/24.18  tff(c_865, plain, (![C_158, G_151, E_155, H_153, B_152, A_154, F_157, D_156]: (k2_xboole_0(k5_enumset1(A_154, B_152, C_158, D_156, E_155, F_157, G_151), k1_tarski(H_153))=k6_enumset1(A_154, B_152, C_158, D_156, E_155, F_157, G_151, H_153))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.63/24.18  tff(c_874, plain, (![A_35, F_40, B_36, H_153, C_37, D_38, E_39]: (k6_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40, H_153)=k2_xboole_0(k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40), k1_tarski(H_153)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_865])).
% 34.63/24.18  tff(c_1488, plain, (![B_211, D_210, A_205, E_209, F_207, H_206, C_208]: (k2_xboole_0(k4_enumset1(A_205, B_211, C_208, D_210, E_209, F_207), k1_tarski(H_206))=k5_enumset1(A_205, B_211, C_208, D_210, E_209, F_207, H_206))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_874])).
% 34.63/24.18  tff(c_1497, plain, (![D_33, A_30, C_32, B_31, E_34, H_206]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, H_206)=k2_xboole_0(k3_enumset1(A_30, B_31, C_32, D_33, E_34), k1_tarski(H_206)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1488])).
% 34.63/24.18  tff(c_1501, plain, (![H_217, A_214, D_216, C_212, B_213, E_215]: (k2_xboole_0(k3_enumset1(A_214, B_213, C_212, D_216, E_215), k1_tarski(H_217))=k4_enumset1(A_214, B_213, C_212, D_216, E_215, H_217))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1497])).
% 34.63/24.18  tff(c_1510, plain, (![B_27, D_29, H_217, A_26, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, H_217)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(H_217)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1501])).
% 34.63/24.18  tff(c_1514, plain, (![B_219, C_222, A_220, H_221, D_218]: (k2_xboole_0(k2_enumset1(A_220, B_219, C_222, D_218), k1_tarski(H_221))=k3_enumset1(A_220, B_219, C_222, D_218, H_221))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1510])).
% 34.63/24.18  tff(c_1526, plain, (![A_23, B_24, C_25, H_221]: (k3_enumset1(A_23, A_23, B_24, C_25, H_221)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(H_221)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1514])).
% 34.63/24.18  tff(c_1530, plain, (![A_223, B_224, C_225, H_226]: (k2_xboole_0(k1_enumset1(A_223, B_224, C_225), k1_tarski(H_226))=k2_enumset1(A_223, B_224, C_225, H_226))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1526])).
% 34.63/24.18  tff(c_1555, plain, (![A_227, C_228, B_229, H_230]: (k2_xboole_0(k1_enumset1(A_227, C_228, B_229), k1_tarski(H_230))=k2_enumset1(A_227, B_229, C_228, H_230))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1530])).
% 34.63/24.18  tff(c_1529, plain, (![A_23, B_24, C_25, H_221]: (k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(H_221))=k2_enumset1(A_23, B_24, C_25, H_221))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1526])).
% 34.63/24.18  tff(c_1561, plain, (![A_227, C_228, B_229, H_230]: (k2_enumset1(A_227, C_228, B_229, H_230)=k2_enumset1(A_227, B_229, C_228, H_230))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_1529])).
% 34.63/24.18  tff(c_36, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 34.63/24.18  tff(c_1651, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_36])).
% 34.63/24.18  tff(c_63716, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_1651])).
% 34.63/24.18  tff(c_63719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_63716])).
% 34.63/24.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.63/24.18  
% 34.63/24.18  Inference rules
% 34.63/24.18  ----------------------
% 34.63/24.18  #Ref     : 0
% 34.63/24.18  #Sup     : 15787
% 34.63/24.18  #Fact    : 0
% 34.63/24.18  #Define  : 0
% 34.63/24.18  #Split   : 0
% 34.63/24.18  #Chain   : 0
% 34.63/24.18  #Close   : 0
% 34.63/24.18  
% 34.63/24.18  Ordering : KBO
% 34.63/24.18  
% 34.63/24.18  Simplification rules
% 34.63/24.18  ----------------------
% 34.63/24.18  #Subsume      : 1893
% 34.63/24.18  #Demod        : 26392
% 34.63/24.18  #Tautology    : 5205
% 34.63/24.18  #SimpNegUnit  : 0
% 34.63/24.18  #BackRed      : 2
% 34.63/24.18  
% 34.63/24.18  #Partial instantiations: 0
% 34.63/24.18  #Strategies tried      : 1
% 34.63/24.18  
% 34.63/24.18  Timing (in seconds)
% 34.63/24.18  ----------------------
% 34.63/24.19  Preprocessing        : 0.34
% 34.63/24.19  Parsing              : 0.18
% 34.63/24.19  CNF conversion       : 0.02
% 34.63/24.19  Main loop            : 23.02
% 34.63/24.19  Inferencing          : 4.92
% 34.63/24.19  Reduction            : 13.93
% 34.63/24.19  Demodulation         : 12.83
% 34.63/24.19  BG Simplification    : 0.77
% 34.63/24.19  Subsumption          : 2.84
% 34.63/24.19  Abstraction          : 1.65
% 34.63/24.19  MUC search           : 0.00
% 34.63/24.19  Cooper               : 0.00
% 34.63/24.19  Total                : 23.40
% 34.63/24.19  Index Insertion      : 0.00
% 34.63/24.19  Index Deletion       : 0.00
% 34.63/24.19  Index Matching       : 0.00
% 34.63/24.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
