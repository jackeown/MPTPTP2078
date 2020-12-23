%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:16 EST 2020

% Result     : Theorem 14.71s
% Output     : CNFRefutation 14.71s
% Verified   : 
% Statistics : Number of formulae       :  187 (1394 expanded)
%              Number of leaves         :   32 ( 475 expanded)
%              Depth                    :   21
%              Number of atoms          :  251 (2499 expanded)
%              Number of equality atoms :  174 (1458 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_46,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_53,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    ! [B_49,A_50] :
      ( r1_xboole_0(B_49,A_50)
      | ~ r1_xboole_0(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_168,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = A_59
      | ~ r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_138,c_168])).

tff(c_528,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_570,plain,(
    ! [A_21] : k3_xboole_0(A_21,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_528])).

tff(c_1036,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_1'(A_105,B_106),k3_xboole_0(A_105,B_106))
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4006,plain,(
    ! [A_187] :
      ( r2_hidden('#skF_1'(A_187,A_187),A_187)
      | r1_xboole_0(A_187,A_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1036])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [A_44,B_45] : r1_tarski(k4_xboole_0(A_44,B_45),A_44) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_155,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_166,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_155])).

tff(c_306,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,(
    ! [B_67,A_66] :
      ( r1_xboole_0(B_67,A_66)
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_598,plain,(
    ! [A_86] : k3_xboole_0(A_86,A_86) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_528])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1098,plain,(
    ! [A_109,C_110] :
      ( ~ r1_xboole_0(A_109,A_109)
      | ~ r2_hidden(C_110,A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_8])).

tff(c_1110,plain,(
    ! [C_110,A_66] :
      ( ~ r2_hidden(C_110,A_66)
      | k4_xboole_0(A_66,A_66) != A_66 ) ),
    inference(resolution,[status(thm)],[c_313,c_1098])).

tff(c_1124,plain,(
    ! [C_110,A_66] :
      ( ~ r2_hidden(C_110,A_66)
      | k1_xboole_0 != A_66 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_1110])).

tff(c_4023,plain,(
    ! [A_187] :
      ( k1_xboole_0 != A_187
      | r1_xboole_0(A_187,A_187) ) ),
    inference(resolution,[status(thm)],[c_4006,c_1124])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1208,plain,(
    ! [C_115,D_116,A_117,B_118] :
      ( ~ r1_xboole_0(C_115,D_116)
      | r1_xboole_0(k2_zfmisc_1(A_117,C_115),k2_zfmisc_1(B_118,D_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6711,plain,(
    ! [B_230,D_231,A_232,C_233] :
      ( r1_xboole_0(k2_zfmisc_1(B_230,D_231),k2_zfmisc_1(A_232,C_233))
      | ~ r1_xboole_0(C_233,D_231) ) ),
    inference(resolution,[status(thm)],[c_1208,c_4])).

tff(c_612,plain,(
    ! [A_86,C_9] :
      ( ~ r1_xboole_0(A_86,A_86)
      | ~ r2_hidden(C_9,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_8])).

tff(c_7037,plain,(
    ! [C_238,A_239,C_240] :
      ( ~ r2_hidden(C_238,k2_zfmisc_1(A_239,C_240))
      | ~ r1_xboole_0(C_240,C_240) ) ),
    inference(resolution,[status(thm)],[c_6711,c_612])).

tff(c_7054,plain,(
    ! [C_241,A_242] :
      ( ~ r1_xboole_0(C_241,C_241)
      | k2_zfmisc_1(A_242,C_241) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_7037])).

tff(c_7132,plain,(
    ! [A_242] : k2_zfmisc_1(A_242,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4023,c_7054])).

tff(c_52,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_635,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( ~ r1_xboole_0(A_87,B_88)
      | r1_xboole_0(k2_zfmisc_1(A_87,C_89),k2_zfmisc_1(B_88,D_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_720,plain,(
    ! [B_95,D_96] :
      ( ~ r1_xboole_0('#skF_5',B_95)
      | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(B_95,D_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_635])).

tff(c_731,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_5')
    | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_720])).

tff(c_3160,plain,(
    ~ r1_xboole_0('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_731])).

tff(c_3169,plain,(
    k4_xboole_0('#skF_5','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_313,c_3160])).

tff(c_3178,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_3169])).

tff(c_1512,plain,(
    ! [C_129,A_130,B_131] : k4_xboole_0(k2_zfmisc_1(C_129,A_130),k2_zfmisc_1(C_129,B_131)) = k2_zfmisc_1(C_129,k4_xboole_0(A_130,B_131)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7356,plain,(
    ! [B_245] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',B_245)) = k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6',B_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1512])).

tff(c_38,plain,(
    ! [A_31,C_33,B_32] : k4_xboole_0(k2_zfmisc_1(A_31,C_33),k2_zfmisc_1(B_32,C_33)) = k2_zfmisc_1(k4_xboole_0(A_31,B_32),C_33) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7404,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') = k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7356,c_38])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_167,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_1574,plain,(
    ! [A_130] : k4_xboole_0(k2_zfmisc_1('#skF_5',A_130),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_5',k4_xboole_0(A_130,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1512])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8942,plain,(
    ! [A_260,C_261,B_262,D_263] :
      ( k4_xboole_0(k2_zfmisc_1(A_260,C_261),k2_zfmisc_1(B_262,D_263)) = k2_zfmisc_1(A_260,C_261)
      | ~ r1_xboole_0(A_260,B_262) ) ),
    inference(resolution,[status(thm)],[c_635,c_26])).

tff(c_9133,plain,(
    ! [A_260,C_261] :
      ( k4_xboole_0(k2_zfmisc_1(A_260,C_261),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1(A_260,C_261)
      | ~ r1_xboole_0(A_260,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8942])).

tff(c_21559,plain,
    ( k4_xboole_0(k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4')
    | ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_9133])).

tff(c_21707,plain,(
    k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7132,c_7404,c_167,c_1574,c_21559])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | k2_zfmisc_1(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21903,plain,
    ( k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_21707,c_30])).

tff(c_21985,plain,(
    k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3178,c_21903])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21671,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0
    | k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_30])).

tff(c_21723,plain,
    ( k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0
    | k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_21671])).

tff(c_22858,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_21985,c_21723])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_371,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(B_70,A_71)
      | k4_xboole_0(A_71,B_70) != A_71 ) ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_2204,plain,(
    ! [B_152,A_153] :
      ( k4_xboole_0(B_152,A_153) = B_152
      | k4_xboole_0(A_153,B_152) != A_153 ) ),
    inference(resolution,[status(thm)],[c_371,c_26])).

tff(c_2220,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = A_16
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2204])).

tff(c_2234,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2220])).

tff(c_23017,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_22858,c_2234])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_744,plain,(
    ! [A_97,B_98] : k4_xboole_0(k3_xboole_0(A_97,B_98),A_97) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_167])).

tff(c_788,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_744])).

tff(c_3630,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(A_176,B_177) = A_176
      | k4_xboole_0(A_176,B_177) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2220])).

tff(c_4418,plain,(
    ! [B_194,A_195] : k3_xboole_0(k3_xboole_0(B_194,A_195),A_195) = k3_xboole_0(B_194,A_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_3630])).

tff(c_4573,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4418])).

tff(c_23120,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k3_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23017,c_4573])).

tff(c_23230,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_23120])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | k4_xboole_0(B_15,A_14) != k4_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22122,plain,
    ( '#skF_6' = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21985,c_16])).

tff(c_24054,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22122])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3181,plain,(
    ! [C_168,A_169,B_170] : r1_xboole_0(k2_zfmisc_1(C_168,k4_xboole_0(A_169,B_170)),k2_zfmisc_1(C_168,B_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_24])).

tff(c_3444,plain,(
    ! [A_173] : r1_xboole_0(k2_zfmisc_1('#skF_5',k4_xboole_0(A_173,'#skF_6')),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3181])).

tff(c_420,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1614,plain,(
    ! [B_134,A_135,C_136] :
      ( ~ r1_xboole_0(B_134,A_135)
      | ~ r2_hidden(C_136,k3_xboole_0(A_135,B_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_420])).

tff(c_1652,plain,(
    ! [B_134,A_135] :
      ( ~ r1_xboole_0(B_134,A_135)
      | k3_xboole_0(A_135,B_134) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1614])).

tff(c_29801,plain,(
    ! [A_436] : k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k4_xboole_0(A_436,'#skF_6'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3444,c_1652])).

tff(c_2582,plain,(
    ! [A_158,C_159,B_160,D_161] : k3_xboole_0(k2_zfmisc_1(A_158,C_159),k2_zfmisc_1(B_160,D_161)) = k2_zfmisc_1(k3_xboole_0(A_158,B_160),k3_xboole_0(C_159,D_161)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2644,plain,(
    ! [B_160,D_161,A_158,C_159] : k3_xboole_0(k2_zfmisc_1(B_160,D_161),k2_zfmisc_1(A_158,C_159)) = k2_zfmisc_1(k3_xboole_0(A_158,B_160),k3_xboole_0(C_159,D_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2582])).

tff(c_29881,plain,(
    ! [A_436] : k2_zfmisc_1(k3_xboole_0('#skF_5','#skF_3'),k3_xboole_0(k4_xboole_0(A_436,'#skF_6'),'#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29801,c_2644])).

tff(c_30174,plain,(
    ! [A_438] : k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',k4_xboole_0(A_438,'#skF_6'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23017,c_2,c_2,c_29881])).

tff(c_30339,plain,(
    ! [A_438] :
      ( k3_xboole_0('#skF_4',k4_xboole_0(A_438,'#skF_6')) = k1_xboole_0
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30174,c_30])).

tff(c_30471,plain,(
    ! [A_439] : k3_xboole_0('#skF_4',k4_xboole_0(A_439,'#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_30339])).

tff(c_573,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_528])).

tff(c_1971,plain,(
    ! [A_147,B_148] : k3_xboole_0(k4_xboole_0(A_147,B_148),A_147) = k4_xboole_0(A_147,B_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_573])).

tff(c_2018,plain,(
    ! [A_147,B_148] : k3_xboole_0(A_147,k4_xboole_0(A_147,B_148)) = k4_xboole_0(A_147,B_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_2])).

tff(c_30596,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30471,c_2018])).

tff(c_30740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24054,c_30596])).

tff(c_30741,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22122])).

tff(c_40,plain,(
    ! [C_33,A_31,B_32] : k4_xboole_0(k2_zfmisc_1(C_33,A_31),k2_zfmisc_1(C_33,B_32)) = k2_zfmisc_1(C_33,k4_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2095,plain,(
    ! [A_149,C_150,B_151] : k4_xboole_0(k2_zfmisc_1(A_149,C_150),k2_zfmisc_1(B_151,C_150)) = k2_zfmisc_1(k4_xboole_0(A_149,B_151),C_150) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8059,plain,(
    ! [B_251] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(B_251,'#skF_6')) = k2_zfmisc_1(k4_xboole_0('#skF_5',B_251),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2095])).

tff(c_8199,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_5','#skF_3'),'#skF_6') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8059])).

tff(c_30750,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_5','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30741,c_30741,c_8199])).

tff(c_30784,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_5','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_166,c_30750])).

tff(c_31128,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30784,c_30])).

tff(c_31202,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31128])).

tff(c_31279,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_31202,c_2234])).

tff(c_31402,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23230,c_31279])).

tff(c_31404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_31402])).

tff(c_31406,plain,(
    r1_xboole_0('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_731])).

tff(c_31409,plain,(
    k3_xboole_0('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31406,c_1652])).

tff(c_31421,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_31409])).

tff(c_34,plain,(
    ! [B_26] : k2_zfmisc_1(k1_xboole_0,B_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_31460,plain,(
    ! [B_26] : k2_zfmisc_1('#skF_5',B_26) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31421,c_31421,c_34])).

tff(c_31542,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31460,c_52])).

tff(c_406,plain,(
    ! [B_74,A_75] :
      ( k1_xboole_0 = B_74
      | k1_xboole_0 = A_75
      | k2_zfmisc_1(A_75,B_74) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_409,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_406])).

tff(c_630,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_31443,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31421,c_630])).

tff(c_32213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31542,c_31443])).

tff(c_32214,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_32216,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32214])).

tff(c_32271,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32216,c_50])).

tff(c_32270,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32216,c_48])).

tff(c_32215,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_32354,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32216,c_32215])).

tff(c_34737,plain,(
    ! [B_545,A_546] :
      ( B_545 = '#skF_6'
      | A_546 = '#skF_6'
      | k2_zfmisc_1(A_546,B_545) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32216,c_32216,c_32216,c_30])).

tff(c_34773,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_32354,c_34737])).

tff(c_34802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32271,c_32270,c_34773])).

tff(c_34803,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32214])).

tff(c_34822,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34803,c_48])).

tff(c_34878,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34803,c_32215])).

tff(c_37297,plain,(
    ! [B_634,A_635] :
      ( B_634 = '#skF_5'
      | A_635 = '#skF_5'
      | k2_zfmisc_1(A_635,B_634) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34803,c_34803,c_34803,c_30])).

tff(c_37333,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_34878,c_37297])).

tff(c_37362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_34822,c_37333])).

tff(c_37363,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_37410,plain,(
    ! [A_642,B_643] : r1_tarski(k4_xboole_0(A_642,B_643),A_642) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37413,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_37410])).

tff(c_37471,plain,(
    ! [A_655,B_656] :
      ( k4_xboole_0(A_655,B_656) = k1_xboole_0
      | ~ r1_tarski(A_655,B_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_37482,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37413,c_37471])).

tff(c_37364,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_37404,plain,(
    k2_zfmisc_1('#skF_3','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37364,c_52])).

tff(c_38805,plain,(
    ! [A_725,C_726,B_727] : k4_xboole_0(k2_zfmisc_1(A_725,C_726),k2_zfmisc_1(B_727,C_726)) = k2_zfmisc_1(k4_xboole_0(A_725,B_727),C_726) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40094,plain,(
    ! [B_758] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(B_758,'#skF_6')) = k2_zfmisc_1(k4_xboole_0('#skF_3',B_758),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37404,c_38805])).

tff(c_40124,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_3'),'#skF_6') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40094,c_40])).

tff(c_40192,plain,(
    k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37482,c_40124])).

tff(c_40242,plain,
    ( k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_40192,c_30])).

tff(c_40264,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40242])).

tff(c_32,plain,(
    ! [A_25] : k2_zfmisc_1(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_39036,plain,(
    ! [C_735,A_736,B_737] : k4_xboole_0(k2_zfmisc_1(C_735,A_736),k2_zfmisc_1(C_735,B_737)) = k2_zfmisc_1(C_735,k4_xboole_0(A_736,B_737)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_39103,plain,(
    ! [B_737] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3',B_737)) = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6',B_737)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37404,c_39036])).

tff(c_42621,plain,(
    ! [B_795] : k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6',B_795)) = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4',B_795)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39103])).

tff(c_42685,plain,(
    ! [B_795] :
      ( k4_xboole_0('#skF_6',B_795) = k1_xboole_0
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4',B_795)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42621,c_30])).

tff(c_43066,plain,(
    ! [B_800] :
      ( k4_xboole_0('#skF_6',B_800) = k1_xboole_0
      | k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4',B_800)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42685])).

tff(c_43093,plain,
    ( k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0
    | k2_zfmisc_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37482,c_43066])).

tff(c_43103,plain,(
    k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43093])).

tff(c_43184,plain,
    ( '#skF_6' = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43103,c_16])).

tff(c_43248,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40264,c_43184])).

tff(c_43250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37363,c_43248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.71/5.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/5.72  
% 14.71/5.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/5.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 14.71/5.72  
% 14.71/5.72  %Foreground sorts:
% 14.71/5.72  
% 14.71/5.72  
% 14.71/5.72  %Background operators:
% 14.71/5.72  
% 14.71/5.72  
% 14.71/5.72  %Foreground operators:
% 14.71/5.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.71/5.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.71/5.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.71/5.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.71/5.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.71/5.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.71/5.72  tff('#skF_5', type, '#skF_5': $i).
% 14.71/5.72  tff('#skF_6', type, '#skF_6': $i).
% 14.71/5.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.71/5.72  tff('#skF_3', type, '#skF_3': $i).
% 14.71/5.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.71/5.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.71/5.72  tff('#skF_4', type, '#skF_4': $i).
% 14.71/5.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.71/5.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.71/5.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.71/5.72  
% 14.71/5.75  tff(f_102, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 14.71/5.75  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 14.71/5.75  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.71/5.75  tff(f_73, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 14.71/5.75  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.71/5.75  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.71/5.75  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.71/5.75  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.71/5.75  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.71/5.75  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.71/5.75  tff(f_91, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 14.71/5.75  tff(f_85, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 14.71/5.75  tff(f_79, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.71/5.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.71/5.75  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 14.71/5.75  tff(f_81, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 14.71/5.75  tff(c_46, plain, ('#skF_6'!='#skF_4' | '#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/5.75  tff(c_53, plain, ('#skF_5'!='#skF_3'), inference(splitLeft, [status(thm)], [c_46])).
% 14.71/5.75  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.71/5.75  tff(c_132, plain, (![B_49, A_50]: (r1_xboole_0(B_49, A_50) | ~r1_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.71/5.75  tff(c_138, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_24, c_132])).
% 14.71/5.75  tff(c_168, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=A_59 | ~r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.71/5.75  tff(c_181, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_138, c_168])).
% 14.71/5.75  tff(c_528, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.71/5.75  tff(c_570, plain, (![A_21]: (k3_xboole_0(A_21, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_181, c_528])).
% 14.71/5.75  tff(c_1036, plain, (![A_105, B_106]: (r2_hidden('#skF_1'(A_105, B_106), k3_xboole_0(A_105, B_106)) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.71/5.75  tff(c_4006, plain, (![A_187]: (r2_hidden('#skF_1'(A_187, A_187), A_187) | r1_xboole_0(A_187, A_187))), inference(superposition, [status(thm), theory('equality')], [c_570, c_1036])).
% 14.71/5.75  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.71/5.75  tff(c_94, plain, (![A_44, B_45]: (r1_tarski(k4_xboole_0(A_44, B_45), A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.71/5.75  tff(c_97, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 14.71/5.75  tff(c_155, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.71/5.75  tff(c_166, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_155])).
% 14.71/5.75  tff(c_306, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k4_xboole_0(A_66, B_67)!=A_66)), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.71/5.75  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.71/5.75  tff(c_313, plain, (![B_67, A_66]: (r1_xboole_0(B_67, A_66) | k4_xboole_0(A_66, B_67)!=A_66)), inference(resolution, [status(thm)], [c_306, c_4])).
% 14.71/5.75  tff(c_598, plain, (![A_86]: (k3_xboole_0(A_86, A_86)=A_86)), inference(superposition, [status(thm), theory('equality')], [c_181, c_528])).
% 14.71/5.75  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.71/5.75  tff(c_1098, plain, (![A_109, C_110]: (~r1_xboole_0(A_109, A_109) | ~r2_hidden(C_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_598, c_8])).
% 14.71/5.75  tff(c_1110, plain, (![C_110, A_66]: (~r2_hidden(C_110, A_66) | k4_xboole_0(A_66, A_66)!=A_66)), inference(resolution, [status(thm)], [c_313, c_1098])).
% 14.71/5.75  tff(c_1124, plain, (![C_110, A_66]: (~r2_hidden(C_110, A_66) | k1_xboole_0!=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_1110])).
% 14.71/5.75  tff(c_4023, plain, (![A_187]: (k1_xboole_0!=A_187 | r1_xboole_0(A_187, A_187))), inference(resolution, [status(thm)], [c_4006, c_1124])).
% 14.71/5.75  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.71/5.75  tff(c_1208, plain, (![C_115, D_116, A_117, B_118]: (~r1_xboole_0(C_115, D_116) | r1_xboole_0(k2_zfmisc_1(A_117, C_115), k2_zfmisc_1(B_118, D_116)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.71/5.75  tff(c_6711, plain, (![B_230, D_231, A_232, C_233]: (r1_xboole_0(k2_zfmisc_1(B_230, D_231), k2_zfmisc_1(A_232, C_233)) | ~r1_xboole_0(C_233, D_231))), inference(resolution, [status(thm)], [c_1208, c_4])).
% 14.71/5.75  tff(c_612, plain, (![A_86, C_9]: (~r1_xboole_0(A_86, A_86) | ~r2_hidden(C_9, A_86))), inference(superposition, [status(thm), theory('equality')], [c_598, c_8])).
% 14.71/5.75  tff(c_7037, plain, (![C_238, A_239, C_240]: (~r2_hidden(C_238, k2_zfmisc_1(A_239, C_240)) | ~r1_xboole_0(C_240, C_240))), inference(resolution, [status(thm)], [c_6711, c_612])).
% 14.71/5.75  tff(c_7054, plain, (![C_241, A_242]: (~r1_xboole_0(C_241, C_241) | k2_zfmisc_1(A_242, C_241)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_7037])).
% 14.71/5.75  tff(c_7132, plain, (![A_242]: (k2_zfmisc_1(A_242, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4023, c_7054])).
% 14.71/5.75  tff(c_52, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/5.75  tff(c_635, plain, (![A_87, B_88, C_89, D_90]: (~r1_xboole_0(A_87, B_88) | r1_xboole_0(k2_zfmisc_1(A_87, C_89), k2_zfmisc_1(B_88, D_90)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.71/5.75  tff(c_720, plain, (![B_95, D_96]: (~r1_xboole_0('#skF_5', B_95) | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(B_95, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_635])).
% 14.71/5.75  tff(c_731, plain, (~r1_xboole_0('#skF_5', '#skF_5') | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_720])).
% 14.71/5.75  tff(c_3160, plain, (~r1_xboole_0('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_731])).
% 14.71/5.75  tff(c_3169, plain, (k4_xboole_0('#skF_5', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_313, c_3160])).
% 14.71/5.75  tff(c_3178, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_3169])).
% 14.71/5.75  tff(c_1512, plain, (![C_129, A_130, B_131]: (k4_xboole_0(k2_zfmisc_1(C_129, A_130), k2_zfmisc_1(C_129, B_131))=k2_zfmisc_1(C_129, k4_xboole_0(A_130, B_131)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_7356, plain, (![B_245]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', B_245))=k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', B_245)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1512])).
% 14.71/5.75  tff(c_38, plain, (![A_31, C_33, B_32]: (k4_xboole_0(k2_zfmisc_1(A_31, C_33), k2_zfmisc_1(B_32, C_33))=k2_zfmisc_1(k4_xboole_0(A_31, B_32), C_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_7404, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')=k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7356, c_38])).
% 14.71/5.75  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.71/5.75  tff(c_167, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_155])).
% 14.71/5.75  tff(c_1574, plain, (![A_130]: (k4_xboole_0(k2_zfmisc_1('#skF_5', A_130), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_5', k4_xboole_0(A_130, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1512])).
% 14.71/5.75  tff(c_26, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.71/5.75  tff(c_8942, plain, (![A_260, C_261, B_262, D_263]: (k4_xboole_0(k2_zfmisc_1(A_260, C_261), k2_zfmisc_1(B_262, D_263))=k2_zfmisc_1(A_260, C_261) | ~r1_xboole_0(A_260, B_262))), inference(resolution, [status(thm)], [c_635, c_26])).
% 14.71/5.75  tff(c_9133, plain, (![A_260, C_261]: (k4_xboole_0(k2_zfmisc_1(A_260, C_261), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1(A_260, C_261) | ~r1_xboole_0(A_260, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8942])).
% 14.71/5.75  tff(c_21559, plain, (k4_xboole_0(k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4')), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4') | ~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7404, c_9133])).
% 14.71/5.75  tff(c_21707, plain, (k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7132, c_7404, c_167, c_1574, c_21559])).
% 14.71/5.75  tff(c_30, plain, (![B_26, A_25]: (k1_xboole_0=B_26 | k1_xboole_0=A_25 | k2_zfmisc_1(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.71/5.75  tff(c_21903, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_21707, c_30])).
% 14.71/5.75  tff(c_21985, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3178, c_21903])).
% 14.71/5.75  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/5.75  tff(c_21671, plain, (k1_xboole_0='#skF_4' | k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7404, c_30])).
% 14.71/5.75  tff(c_21723, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_21671])).
% 14.71/5.75  tff(c_22858, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7132, c_21985, c_21723])).
% 14.71/5.75  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.71/5.75  tff(c_371, plain, (![B_70, A_71]: (r1_xboole_0(B_70, A_71) | k4_xboole_0(A_71, B_70)!=A_71)), inference(resolution, [status(thm)], [c_306, c_4])).
% 14.71/5.75  tff(c_2204, plain, (![B_152, A_153]: (k4_xboole_0(B_152, A_153)=B_152 | k4_xboole_0(A_153, B_152)!=A_153)), inference(resolution, [status(thm)], [c_371, c_26])).
% 14.71/5.75  tff(c_2220, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=A_16 | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_167, c_2204])).
% 14.71/5.75  tff(c_2234, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2220])).
% 14.71/5.75  tff(c_23017, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_22858, c_2234])).
% 14.71/5.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.71/5.75  tff(c_744, plain, (![A_97, B_98]: (k4_xboole_0(k3_xboole_0(A_97, B_98), A_97)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_528, c_167])).
% 14.71/5.75  tff(c_788, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_744])).
% 14.71/5.75  tff(c_3630, plain, (![A_176, B_177]: (k3_xboole_0(A_176, B_177)=A_176 | k4_xboole_0(A_176, B_177)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2220])).
% 14.71/5.75  tff(c_4418, plain, (![B_194, A_195]: (k3_xboole_0(k3_xboole_0(B_194, A_195), A_195)=k3_xboole_0(B_194, A_195))), inference(superposition, [status(thm), theory('equality')], [c_788, c_3630])).
% 14.71/5.75  tff(c_4573, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4418])).
% 14.71/5.75  tff(c_23120, plain, (k3_xboole_0('#skF_5', '#skF_3')=k3_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23017, c_4573])).
% 14.71/5.75  tff(c_23230, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_570, c_23120])).
% 14.71/5.75  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | k4_xboole_0(B_15, A_14)!=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.71/5.75  tff(c_22122, plain, ('#skF_6'='#skF_4' | k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21985, c_16])).
% 14.71/5.75  tff(c_24054, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22122])).
% 14.71/5.75  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/5.75  tff(c_3181, plain, (![C_168, A_169, B_170]: (r1_xboole_0(k2_zfmisc_1(C_168, k4_xboole_0(A_169, B_170)), k2_zfmisc_1(C_168, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_1512, c_24])).
% 14.71/5.75  tff(c_3444, plain, (![A_173]: (r1_xboole_0(k2_zfmisc_1('#skF_5', k4_xboole_0(A_173, '#skF_6')), k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_3181])).
% 14.71/5.75  tff(c_420, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.71/5.75  tff(c_1614, plain, (![B_134, A_135, C_136]: (~r1_xboole_0(B_134, A_135) | ~r2_hidden(C_136, k3_xboole_0(A_135, B_134)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_420])).
% 14.71/5.75  tff(c_1652, plain, (![B_134, A_135]: (~r1_xboole_0(B_134, A_135) | k3_xboole_0(A_135, B_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1614])).
% 14.71/5.75  tff(c_29801, plain, (![A_436]: (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k4_xboole_0(A_436, '#skF_6')))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3444, c_1652])).
% 14.71/5.75  tff(c_2582, plain, (![A_158, C_159, B_160, D_161]: (k3_xboole_0(k2_zfmisc_1(A_158, C_159), k2_zfmisc_1(B_160, D_161))=k2_zfmisc_1(k3_xboole_0(A_158, B_160), k3_xboole_0(C_159, D_161)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.71/5.75  tff(c_2644, plain, (![B_160, D_161, A_158, C_159]: (k3_xboole_0(k2_zfmisc_1(B_160, D_161), k2_zfmisc_1(A_158, C_159))=k2_zfmisc_1(k3_xboole_0(A_158, B_160), k3_xboole_0(C_159, D_161)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2582])).
% 14.71/5.75  tff(c_29881, plain, (![A_436]: (k2_zfmisc_1(k3_xboole_0('#skF_5', '#skF_3'), k3_xboole_0(k4_xboole_0(A_436, '#skF_6'), '#skF_4'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_29801, c_2644])).
% 14.71/5.75  tff(c_30174, plain, (![A_438]: (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', k4_xboole_0(A_438, '#skF_6')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23017, c_2, c_2, c_29881])).
% 14.71/5.75  tff(c_30339, plain, (![A_438]: (k3_xboole_0('#skF_4', k4_xboole_0(A_438, '#skF_6'))=k1_xboole_0 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30174, c_30])).
% 14.71/5.75  tff(c_30471, plain, (![A_439]: (k3_xboole_0('#skF_4', k4_xboole_0(A_439, '#skF_6'))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_30339])).
% 14.71/5.75  tff(c_573, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_167, c_528])).
% 14.71/5.75  tff(c_1971, plain, (![A_147, B_148]: (k3_xboole_0(k4_xboole_0(A_147, B_148), A_147)=k4_xboole_0(A_147, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_573])).
% 14.71/5.75  tff(c_2018, plain, (![A_147, B_148]: (k3_xboole_0(A_147, k4_xboole_0(A_147, B_148))=k4_xboole_0(A_147, B_148))), inference(superposition, [status(thm), theory('equality')], [c_1971, c_2])).
% 14.71/5.75  tff(c_30596, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30471, c_2018])).
% 14.71/5.75  tff(c_30740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24054, c_30596])).
% 14.71/5.75  tff(c_30741, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_22122])).
% 14.71/5.75  tff(c_40, plain, (![C_33, A_31, B_32]: (k4_xboole_0(k2_zfmisc_1(C_33, A_31), k2_zfmisc_1(C_33, B_32))=k2_zfmisc_1(C_33, k4_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_2095, plain, (![A_149, C_150, B_151]: (k4_xboole_0(k2_zfmisc_1(A_149, C_150), k2_zfmisc_1(B_151, C_150))=k2_zfmisc_1(k4_xboole_0(A_149, B_151), C_150))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_8059, plain, (![B_251]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(B_251, '#skF_6'))=k2_zfmisc_1(k4_xboole_0('#skF_5', B_251), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2095])).
% 14.71/5.75  tff(c_8199, plain, (k2_zfmisc_1(k4_xboole_0('#skF_5', '#skF_3'), '#skF_6')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_8059])).
% 14.71/5.75  tff(c_30750, plain, (k2_zfmisc_1(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30741, c_30741, c_8199])).
% 14.71/5.75  tff(c_30784, plain, (k2_zfmisc_1(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7132, c_166, c_30750])).
% 14.71/5.75  tff(c_31128, plain, (k1_xboole_0='#skF_4' | k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30784, c_30])).
% 14.71/5.75  tff(c_31202, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_31128])).
% 14.71/5.75  tff(c_31279, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_31202, c_2234])).
% 14.71/5.75  tff(c_31402, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23230, c_31279])).
% 14.71/5.75  tff(c_31404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_31402])).
% 14.71/5.75  tff(c_31406, plain, (r1_xboole_0('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_731])).
% 14.71/5.75  tff(c_31409, plain, (k3_xboole_0('#skF_5', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_31406, c_1652])).
% 14.71/5.75  tff(c_31421, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_570, c_31409])).
% 14.71/5.75  tff(c_34, plain, (![B_26]: (k2_zfmisc_1(k1_xboole_0, B_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.71/5.75  tff(c_31460, plain, (![B_26]: (k2_zfmisc_1('#skF_5', B_26)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31421, c_31421, c_34])).
% 14.71/5.75  tff(c_31542, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31460, c_52])).
% 14.71/5.75  tff(c_406, plain, (![B_74, A_75]: (k1_xboole_0=B_74 | k1_xboole_0=A_75 | k2_zfmisc_1(A_75, B_74)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.71/5.75  tff(c_409, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_52, c_406])).
% 14.71/5.75  tff(c_630, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_409])).
% 14.71/5.75  tff(c_31443, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31421, c_630])).
% 14.71/5.75  tff(c_32213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31542, c_31443])).
% 14.71/5.75  tff(c_32214, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_409])).
% 14.71/5.75  tff(c_32216, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_32214])).
% 14.71/5.75  tff(c_32271, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32216, c_50])).
% 14.71/5.75  tff(c_32270, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32216, c_48])).
% 14.71/5.75  tff(c_32215, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_409])).
% 14.71/5.75  tff(c_32354, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32216, c_32215])).
% 14.71/5.75  tff(c_34737, plain, (![B_545, A_546]: (B_545='#skF_6' | A_546='#skF_6' | k2_zfmisc_1(A_546, B_545)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32216, c_32216, c_32216, c_30])).
% 14.71/5.75  tff(c_34773, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_32354, c_34737])).
% 14.71/5.75  tff(c_34802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32271, c_32270, c_34773])).
% 14.71/5.75  tff(c_34803, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_32214])).
% 14.71/5.75  tff(c_34822, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34803, c_48])).
% 14.71/5.75  tff(c_34878, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34803, c_32215])).
% 14.71/5.75  tff(c_37297, plain, (![B_634, A_635]: (B_634='#skF_5' | A_635='#skF_5' | k2_zfmisc_1(A_635, B_634)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34803, c_34803, c_34803, c_30])).
% 14.71/5.75  tff(c_37333, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_34878, c_37297])).
% 14.71/5.75  tff(c_37362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_34822, c_37333])).
% 14.71/5.75  tff(c_37363, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 14.71/5.75  tff(c_37410, plain, (![A_642, B_643]: (r1_tarski(k4_xboole_0(A_642, B_643), A_642))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.71/5.75  tff(c_37413, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_37410])).
% 14.71/5.75  tff(c_37471, plain, (![A_655, B_656]: (k4_xboole_0(A_655, B_656)=k1_xboole_0 | ~r1_tarski(A_655, B_656))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.71/5.75  tff(c_37482, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37413, c_37471])).
% 14.71/5.75  tff(c_37364, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 14.71/5.75  tff(c_37404, plain, (k2_zfmisc_1('#skF_3', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37364, c_52])).
% 14.71/5.75  tff(c_38805, plain, (![A_725, C_726, B_727]: (k4_xboole_0(k2_zfmisc_1(A_725, C_726), k2_zfmisc_1(B_727, C_726))=k2_zfmisc_1(k4_xboole_0(A_725, B_727), C_726))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_40094, plain, (![B_758]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(B_758, '#skF_6'))=k2_zfmisc_1(k4_xboole_0('#skF_3', B_758), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_37404, c_38805])).
% 14.71/5.75  tff(c_40124, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_3'), '#skF_6')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40094, c_40])).
% 14.71/5.75  tff(c_40192, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_37482, c_40124])).
% 14.71/5.75  tff(c_40242, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_40192, c_30])).
% 14.71/5.75  tff(c_40264, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_40242])).
% 14.71/5.75  tff(c_32, plain, (![A_25]: (k2_zfmisc_1(A_25, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.71/5.75  tff(c_39036, plain, (![C_735, A_736, B_737]: (k4_xboole_0(k2_zfmisc_1(C_735, A_736), k2_zfmisc_1(C_735, B_737))=k2_zfmisc_1(C_735, k4_xboole_0(A_736, B_737)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.71/5.75  tff(c_39103, plain, (![B_737]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', B_737))=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', B_737)))), inference(superposition, [status(thm), theory('equality')], [c_37404, c_39036])).
% 14.71/5.75  tff(c_42621, plain, (![B_795]: (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', B_795))=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', B_795)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39103])).
% 14.71/5.75  tff(c_42685, plain, (![B_795]: (k4_xboole_0('#skF_6', B_795)=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', B_795))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42621, c_30])).
% 14.71/5.75  tff(c_43066, plain, (![B_800]: (k4_xboole_0('#skF_6', B_800)=k1_xboole_0 | k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', B_800))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_42685])).
% 14.71/5.75  tff(c_43093, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0 | k2_zfmisc_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37482, c_43066])).
% 14.71/5.75  tff(c_43103, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_43093])).
% 14.71/5.75  tff(c_43184, plain, ('#skF_6'='#skF_4' | k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43103, c_16])).
% 14.71/5.75  tff(c_43248, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40264, c_43184])).
% 14.71/5.75  tff(c_43250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37363, c_43248])).
% 14.71/5.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/5.75  
% 14.71/5.75  Inference rules
% 14.71/5.75  ----------------------
% 14.71/5.75  #Ref     : 5
% 14.71/5.75  #Sup     : 10886
% 14.71/5.75  #Fact    : 0
% 14.71/5.75  #Define  : 0
% 14.71/5.75  #Split   : 16
% 14.71/5.75  #Chain   : 0
% 14.71/5.75  #Close   : 0
% 14.71/5.75  
% 14.71/5.75  Ordering : KBO
% 14.71/5.75  
% 14.71/5.75  Simplification rules
% 14.71/5.75  ----------------------
% 14.71/5.75  #Subsume      : 2022
% 14.71/5.75  #Demod        : 10510
% 14.71/5.75  #Tautology    : 5722
% 14.71/5.75  #SimpNegUnit  : 242
% 14.71/5.75  #BackRed      : 133
% 14.71/5.75  
% 14.71/5.75  #Partial instantiations: 0
% 14.71/5.75  #Strategies tried      : 1
% 14.71/5.75  
% 14.71/5.75  Timing (in seconds)
% 14.71/5.75  ----------------------
% 14.71/5.75  Preprocessing        : 0.33
% 14.71/5.75  Parsing              : 0.17
% 14.71/5.75  CNF conversion       : 0.02
% 14.71/5.75  Main loop            : 4.62
% 14.71/5.75  Inferencing          : 0.86
% 14.71/5.75  Reduction            : 2.52
% 14.71/5.75  Demodulation         : 2.14
% 14.71/5.75  BG Simplification    : 0.10
% 14.71/5.75  Subsumption          : 0.87
% 14.71/5.75  Abstraction          : 0.16
% 14.71/5.75  MUC search           : 0.00
% 14.71/5.75  Cooper               : 0.00
% 14.71/5.75  Total                : 5.01
% 14.71/5.75  Index Insertion      : 0.00
% 14.71/5.75  Index Deletion       : 0.00
% 14.71/5.75  Index Matching       : 0.00
% 14.71/5.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
