%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 13.79s
% Output     : CNFRefutation 13.85s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 698 expanded)
%              Number of leaves         :   24 ( 248 expanded)
%              Depth                    :   19
%              Number of atoms          :  124 (1321 expanded)
%              Number of equality atoms :   48 ( 437 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_197,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1396,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_117,B_118),B_119),A_117)
      | r1_tarski(k4_xboole_0(A_117,B_118),B_119) ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1452,plain,(
    ! [A_117,B_118] : r1_tarski(k4_xboole_0(A_117,B_118),A_117) ),
    inference(resolution,[status(thm)],[c_1396,c_6])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_109,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_94])).

tff(c_745,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_2'(A_88,B_89,C_90),A_88)
      | r2_hidden('#skF_3'(A_88,B_89,C_90),C_90)
      | k4_xboole_0(A_88,B_89) = C_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_748,plain,(
    ! [A_88,C_90] :
      ( r2_hidden('#skF_3'(A_88,A_88,C_90),C_90)
      | k4_xboole_0(A_88,A_88) = C_90 ) ),
    inference(resolution,[status(thm)],[c_745,c_24])).

tff(c_830,plain,(
    ! [A_88,C_90] :
      ( r2_hidden('#skF_3'(A_88,A_88,C_90),C_90)
      | k3_xboole_0(A_88,k1_xboole_0) = C_90 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_748])).

tff(c_853,plain,(
    ! [A_91,C_92] :
      ( r2_hidden('#skF_3'(A_91,A_91,C_92),C_92)
      | k3_xboole_0(A_91,k1_xboole_0) = C_92 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_748])).

tff(c_176,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_189,plain,(
    ! [D_39,A_17] :
      ( ~ r2_hidden(D_39,k1_xboole_0)
      | ~ r2_hidden(D_39,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_176])).

tff(c_955,plain,(
    ! [A_95,A_96] :
      ( ~ r2_hidden('#skF_3'(A_95,A_95,k1_xboole_0),A_96)
      | k3_xboole_0(A_95,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_853,c_189])).

tff(c_972,plain,(
    ! [A_88] : k3_xboole_0(A_88,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_830,c_955])).

tff(c_981,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_109])).

tff(c_291,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k4_xboole_0(A_60,B_61))
      | r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4787,plain,(
    ! [A_276,A_277,B_278] :
      ( r1_tarski(A_276,k4_xboole_0(A_277,B_278))
      | r2_hidden('#skF_1'(A_276,k4_xboole_0(A_277,B_278)),B_278)
      | ~ r2_hidden('#skF_1'(A_276,k4_xboole_0(A_277,B_278)),A_277) ) ),
    inference(resolution,[status(thm)],[c_291,c_6])).

tff(c_4856,plain,(
    ! [A_279,B_280] :
      ( r2_hidden('#skF_1'(A_279,k4_xboole_0(A_279,B_280)),B_280)
      | r1_tarski(A_279,k4_xboole_0(A_279,B_280)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4787])).

tff(c_190,plain,(
    ! [A_41,B_40,B_4] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_41,B_40),B_4),B_40)
      | r1_tarski(k4_xboole_0(A_41,B_40),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_4953,plain,(
    ! [A_281,B_282] : r1_tarski(k4_xboole_0(A_281,B_282),k4_xboole_0(k4_xboole_0(A_281,B_282),B_282)) ),
    inference(resolution,[status(thm)],[c_4856,c_190])).

tff(c_1458,plain,(
    ! [A_120,B_121] : r1_tarski(k4_xboole_0(A_120,B_121),A_120) ),
    inference(resolution,[status(thm)],[c_1396,c_6])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1481,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,B_121) = A_120
      | ~ r1_tarski(A_120,k4_xboole_0(A_120,B_121)) ) ),
    inference(resolution,[status(thm)],[c_1458,c_28])).

tff(c_5037,plain,(
    ! [A_283,B_284] : k4_xboole_0(k4_xboole_0(A_283,B_284),B_284) = k4_xboole_0(A_283,B_284) ),
    inference(resolution,[status(thm)],[c_4953,c_1481])).

tff(c_5113,plain,(
    ! [A_283,B_284] : k4_xboole_0(k4_xboole_0(A_283,B_284),k4_xboole_0(A_283,B_284)) = k3_xboole_0(k4_xboole_0(A_283,B_284),B_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_5037,c_38])).

tff(c_5193,plain,(
    ! [B_285,A_286] : k3_xboole_0(B_285,k4_xboole_0(A_286,B_285)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_2,c_5113])).

tff(c_103,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_5329,plain,(
    ! [B_285,A_286] : k3_xboole_0(B_285,k4_xboole_0(B_285,k4_xboole_0(A_286,B_285))) = k4_xboole_0(B_285,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5193,c_103])).

tff(c_5414,plain,(
    ! [B_285,A_286] : k3_xboole_0(B_285,k4_xboole_0(B_285,k4_xboole_0(A_286,B_285))) = B_285 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5329])).

tff(c_5751,plain,(
    ! [B_293,A_294] : k3_xboole_0(B_293,k4_xboole_0(B_293,k4_xboole_0(A_294,B_293))) = B_293 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5329])).

tff(c_1564,plain,(
    ! [A_123,B_124] : r1_tarski(k3_xboole_0(A_123,B_124),A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1458])).

tff(c_1750,plain,(
    ! [A_136,B_137] :
      ( k3_xboole_0(A_136,B_137) = A_136
      | ~ r1_tarski(A_136,k3_xboole_0(A_136,B_137)) ) ),
    inference(resolution,[status(thm)],[c_1564,c_28])).

tff(c_1768,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1750])).

tff(c_5866,plain,(
    ! [B_293,A_294] :
      ( k3_xboole_0(k4_xboole_0(B_293,k4_xboole_0(A_294,B_293)),B_293) = k4_xboole_0(B_293,k4_xboole_0(A_294,B_293))
      | ~ r1_tarski(k4_xboole_0(B_293,k4_xboole_0(A_294,B_293)),B_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5751,c_1768])).

tff(c_5967,plain,(
    ! [B_293,A_294] : k4_xboole_0(B_293,k4_xboole_0(A_294,B_293)) = B_293 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_5414,c_2,c_5866])).

tff(c_4853,plain,(
    ! [A_3,B_278] :
      ( r2_hidden('#skF_1'(A_3,k4_xboole_0(A_3,B_278)),B_278)
      | r1_tarski(A_3,k4_xboole_0(A_3,B_278)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4787])).

tff(c_255,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1312,plain,(
    ! [A_112,B_113,B_114] :
      ( r2_hidden('#skF_1'(A_112,B_113),B_114)
      | ~ r1_tarski(A_112,B_114)
      | r1_tarski(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22112,plain,(
    ! [A_491,B_492,B_493,A_494] :
      ( ~ r2_hidden('#skF_1'(A_491,B_492),B_493)
      | ~ r1_tarski(A_491,k4_xboole_0(A_494,B_493))
      | r1_tarski(A_491,B_492) ) ),
    inference(resolution,[status(thm)],[c_1312,c_12])).

tff(c_22153,plain,(
    ! [A_495,A_496,B_497] :
      ( ~ r1_tarski(A_495,k4_xboole_0(A_496,B_497))
      | r1_tarski(A_495,k4_xboole_0(A_495,B_497)) ) ),
    inference(resolution,[status(thm)],[c_4853,c_22112])).

tff(c_22211,plain,(
    ! [A_498,B_499,A_500] :
      ( ~ r1_tarski(A_498,B_499)
      | r1_tarski(A_498,k4_xboole_0(A_498,k4_xboole_0(A_500,B_499))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5967,c_22153])).

tff(c_22334,plain,(
    ! [A_501,B_502] :
      ( ~ r1_tarski(A_501,B_502)
      | r1_tarski(A_501,k3_xboole_0(A_501,B_502)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22211])).

tff(c_1595,plain,(
    ! [B_125,A_126] : r1_tarski(k3_xboole_0(B_125,A_126),A_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1564])).

tff(c_1781,plain,(
    ! [B_138,A_139] :
      ( k3_xboole_0(B_138,A_139) = A_139
      | ~ r1_tarski(A_139,k3_xboole_0(B_138,A_139)) ) ),
    inference(resolution,[status(thm)],[c_1595,c_28])).

tff(c_1796,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1781])).

tff(c_22572,plain,(
    ! [B_505,A_506] :
      ( k3_xboole_0(B_505,A_506) = A_506
      | ~ r1_tarski(A_506,B_505) ) ),
    inference(resolution,[status(thm)],[c_22334,c_1796])).

tff(c_22713,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_22572])).

tff(c_23036,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22713])).

tff(c_46,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22714,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_22572])).

tff(c_5144,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5037])).

tff(c_5189,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5144])).

tff(c_23265,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_4')) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22714,c_5189])).

tff(c_23453,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5967,c_2,c_23265])).

tff(c_40,plain,(
    ! [A_20,C_22,B_21,D_23] : k3_xboole_0(k2_zfmisc_1(A_20,C_22),k2_zfmisc_1(B_21,D_23)) = k2_zfmisc_1(k3_xboole_0(A_20,B_21),k3_xboole_0(C_22,D_23)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_7'),k2_zfmisc_1('#skF_5','#skF_6')) != k2_zfmisc_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_47,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_5'),k3_xboole_0('#skF_7','#skF_6')) != k2_zfmisc_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_49,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_5'),k3_xboole_0('#skF_6','#skF_7')) != k2_zfmisc_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_23761,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_6','#skF_7')) != k2_zfmisc_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23453,c_49])).

tff(c_39226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23036,c_23761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.79/6.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.33  
% 13.79/6.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.33  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 13.79/6.33  
% 13.79/6.33  %Foreground sorts:
% 13.79/6.33  
% 13.79/6.33  
% 13.79/6.33  %Background operators:
% 13.79/6.33  
% 13.79/6.33  
% 13.79/6.33  %Foreground operators:
% 13.79/6.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.79/6.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.79/6.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.79/6.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.79/6.33  tff('#skF_7', type, '#skF_7': $i).
% 13.79/6.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.79/6.33  tff('#skF_5', type, '#skF_5': $i).
% 13.79/6.33  tff('#skF_6', type, '#skF_6': $i).
% 13.79/6.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.79/6.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.79/6.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.79/6.33  tff('#skF_4', type, '#skF_4': $i).
% 13.79/6.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.79/6.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.79/6.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.79/6.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.79/6.33  
% 13.85/6.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.85/6.35  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 13.85/6.35  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.85/6.35  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.85/6.35  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.85/6.35  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.85/6.35  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.85/6.35  tff(f_58, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 13.85/6.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.85/6.35  tff(c_44, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.85/6.35  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.85/6.35  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.85/6.35  tff(c_197, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k4_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_1396, plain, (![A_117, B_118, B_119]: (r2_hidden('#skF_1'(k4_xboole_0(A_117, B_118), B_119), A_117) | r1_tarski(k4_xboole_0(A_117, B_118), B_119))), inference(resolution, [status(thm)], [c_8, c_197])).
% 13.85/6.35  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.85/6.35  tff(c_1452, plain, (![A_117, B_118]: (r1_tarski(k4_xboole_0(A_117, B_118), A_117))), inference(resolution, [status(thm)], [c_1396, c_6])).
% 13.85/6.35  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.85/6.35  tff(c_94, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.85/6.35  tff(c_109, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_94])).
% 13.85/6.35  tff(c_745, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_2'(A_88, B_89, C_90), A_88) | r2_hidden('#skF_3'(A_88, B_89, C_90), C_90) | k4_xboole_0(A_88, B_89)=C_90)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_748, plain, (![A_88, C_90]: (r2_hidden('#skF_3'(A_88, A_88, C_90), C_90) | k4_xboole_0(A_88, A_88)=C_90)), inference(resolution, [status(thm)], [c_745, c_24])).
% 13.85/6.35  tff(c_830, plain, (![A_88, C_90]: (r2_hidden('#skF_3'(A_88, A_88, C_90), C_90) | k3_xboole_0(A_88, k1_xboole_0)=C_90)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_748])).
% 13.85/6.35  tff(c_853, plain, (![A_91, C_92]: (r2_hidden('#skF_3'(A_91, A_91, C_92), C_92) | k3_xboole_0(A_91, k1_xboole_0)=C_92)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_748])).
% 13.85/6.35  tff(c_176, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k4_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_189, plain, (![D_39, A_17]: (~r2_hidden(D_39, k1_xboole_0) | ~r2_hidden(D_39, A_17))), inference(superposition, [status(thm), theory('equality')], [c_36, c_176])).
% 13.85/6.35  tff(c_955, plain, (![A_95, A_96]: (~r2_hidden('#skF_3'(A_95, A_95, k1_xboole_0), A_96) | k3_xboole_0(A_95, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_853, c_189])).
% 13.85/6.35  tff(c_972, plain, (![A_88]: (k3_xboole_0(A_88, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_830, c_955])).
% 13.85/6.35  tff(c_981, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_972, c_109])).
% 13.85/6.35  tff(c_291, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, k4_xboole_0(A_60, B_61)) | r2_hidden(D_59, B_61) | ~r2_hidden(D_59, A_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_4787, plain, (![A_276, A_277, B_278]: (r1_tarski(A_276, k4_xboole_0(A_277, B_278)) | r2_hidden('#skF_1'(A_276, k4_xboole_0(A_277, B_278)), B_278) | ~r2_hidden('#skF_1'(A_276, k4_xboole_0(A_277, B_278)), A_277))), inference(resolution, [status(thm)], [c_291, c_6])).
% 13.85/6.35  tff(c_4856, plain, (![A_279, B_280]: (r2_hidden('#skF_1'(A_279, k4_xboole_0(A_279, B_280)), B_280) | r1_tarski(A_279, k4_xboole_0(A_279, B_280)))), inference(resolution, [status(thm)], [c_8, c_4787])).
% 13.85/6.35  tff(c_190, plain, (![A_41, B_40, B_4]: (~r2_hidden('#skF_1'(k4_xboole_0(A_41, B_40), B_4), B_40) | r1_tarski(k4_xboole_0(A_41, B_40), B_4))), inference(resolution, [status(thm)], [c_8, c_176])).
% 13.85/6.35  tff(c_4953, plain, (![A_281, B_282]: (r1_tarski(k4_xboole_0(A_281, B_282), k4_xboole_0(k4_xboole_0(A_281, B_282), B_282)))), inference(resolution, [status(thm)], [c_4856, c_190])).
% 13.85/6.35  tff(c_1458, plain, (![A_120, B_121]: (r1_tarski(k4_xboole_0(A_120, B_121), A_120))), inference(resolution, [status(thm)], [c_1396, c_6])).
% 13.85/6.35  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.85/6.35  tff(c_1481, plain, (![A_120, B_121]: (k4_xboole_0(A_120, B_121)=A_120 | ~r1_tarski(A_120, k4_xboole_0(A_120, B_121)))), inference(resolution, [status(thm)], [c_1458, c_28])).
% 13.85/6.35  tff(c_5037, plain, (![A_283, B_284]: (k4_xboole_0(k4_xboole_0(A_283, B_284), B_284)=k4_xboole_0(A_283, B_284))), inference(resolution, [status(thm)], [c_4953, c_1481])).
% 13.85/6.35  tff(c_5113, plain, (![A_283, B_284]: (k4_xboole_0(k4_xboole_0(A_283, B_284), k4_xboole_0(A_283, B_284))=k3_xboole_0(k4_xboole_0(A_283, B_284), B_284))), inference(superposition, [status(thm), theory('equality')], [c_5037, c_38])).
% 13.85/6.35  tff(c_5193, plain, (![B_285, A_286]: (k3_xboole_0(B_285, k4_xboole_0(A_286, B_285))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_981, c_2, c_5113])).
% 13.85/6.35  tff(c_103, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_94])).
% 13.85/6.35  tff(c_5329, plain, (![B_285, A_286]: (k3_xboole_0(B_285, k4_xboole_0(B_285, k4_xboole_0(A_286, B_285)))=k4_xboole_0(B_285, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5193, c_103])).
% 13.85/6.35  tff(c_5414, plain, (![B_285, A_286]: (k3_xboole_0(B_285, k4_xboole_0(B_285, k4_xboole_0(A_286, B_285)))=B_285)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5329])).
% 13.85/6.35  tff(c_5751, plain, (![B_293, A_294]: (k3_xboole_0(B_293, k4_xboole_0(B_293, k4_xboole_0(A_294, B_293)))=B_293)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5329])).
% 13.85/6.35  tff(c_1564, plain, (![A_123, B_124]: (r1_tarski(k3_xboole_0(A_123, B_124), A_123))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1458])).
% 13.85/6.35  tff(c_1750, plain, (![A_136, B_137]: (k3_xboole_0(A_136, B_137)=A_136 | ~r1_tarski(A_136, k3_xboole_0(A_136, B_137)))), inference(resolution, [status(thm)], [c_1564, c_28])).
% 13.85/6.35  tff(c_1768, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=B_2 | ~r1_tarski(B_2, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1750])).
% 13.85/6.35  tff(c_5866, plain, (![B_293, A_294]: (k3_xboole_0(k4_xboole_0(B_293, k4_xboole_0(A_294, B_293)), B_293)=k4_xboole_0(B_293, k4_xboole_0(A_294, B_293)) | ~r1_tarski(k4_xboole_0(B_293, k4_xboole_0(A_294, B_293)), B_293))), inference(superposition, [status(thm), theory('equality')], [c_5751, c_1768])).
% 13.85/6.35  tff(c_5967, plain, (![B_293, A_294]: (k4_xboole_0(B_293, k4_xboole_0(A_294, B_293))=B_293)), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_5414, c_2, c_5866])).
% 13.85/6.35  tff(c_4853, plain, (![A_3, B_278]: (r2_hidden('#skF_1'(A_3, k4_xboole_0(A_3, B_278)), B_278) | r1_tarski(A_3, k4_xboole_0(A_3, B_278)))), inference(resolution, [status(thm)], [c_8, c_4787])).
% 13.85/6.35  tff(c_255, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.85/6.35  tff(c_1312, plain, (![A_112, B_113, B_114]: (r2_hidden('#skF_1'(A_112, B_113), B_114) | ~r1_tarski(A_112, B_114) | r1_tarski(A_112, B_113))), inference(resolution, [status(thm)], [c_8, c_255])).
% 13.85/6.35  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.85/6.35  tff(c_22112, plain, (![A_491, B_492, B_493, A_494]: (~r2_hidden('#skF_1'(A_491, B_492), B_493) | ~r1_tarski(A_491, k4_xboole_0(A_494, B_493)) | r1_tarski(A_491, B_492))), inference(resolution, [status(thm)], [c_1312, c_12])).
% 13.85/6.35  tff(c_22153, plain, (![A_495, A_496, B_497]: (~r1_tarski(A_495, k4_xboole_0(A_496, B_497)) | r1_tarski(A_495, k4_xboole_0(A_495, B_497)))), inference(resolution, [status(thm)], [c_4853, c_22112])).
% 13.85/6.35  tff(c_22211, plain, (![A_498, B_499, A_500]: (~r1_tarski(A_498, B_499) | r1_tarski(A_498, k4_xboole_0(A_498, k4_xboole_0(A_500, B_499))))), inference(superposition, [status(thm), theory('equality')], [c_5967, c_22153])).
% 13.85/6.35  tff(c_22334, plain, (![A_501, B_502]: (~r1_tarski(A_501, B_502) | r1_tarski(A_501, k3_xboole_0(A_501, B_502)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_22211])).
% 13.85/6.35  tff(c_1595, plain, (![B_125, A_126]: (r1_tarski(k3_xboole_0(B_125, A_126), A_126))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1564])).
% 13.85/6.35  tff(c_1781, plain, (![B_138, A_139]: (k3_xboole_0(B_138, A_139)=A_139 | ~r1_tarski(A_139, k3_xboole_0(B_138, A_139)))), inference(resolution, [status(thm)], [c_1595, c_28])).
% 13.85/6.35  tff(c_1796, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(B_2, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1781])).
% 13.85/6.35  tff(c_22572, plain, (![B_505, A_506]: (k3_xboole_0(B_505, A_506)=A_506 | ~r1_tarski(A_506, B_505))), inference(resolution, [status(thm)], [c_22334, c_1796])).
% 13.85/6.35  tff(c_22713, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_44, c_22572])).
% 13.85/6.35  tff(c_23036, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2, c_22713])).
% 13.85/6.35  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.85/6.35  tff(c_22714, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_22572])).
% 13.85/6.35  tff(c_5144, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=k4_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5037])).
% 13.85/6.35  tff(c_5189, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5144])).
% 13.85/6.35  tff(c_23265, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_4'))=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22714, c_5189])).
% 13.85/6.35  tff(c_23453, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5967, c_2, c_23265])).
% 13.85/6.35  tff(c_40, plain, (![A_20, C_22, B_21, D_23]: (k3_xboole_0(k2_zfmisc_1(A_20, C_22), k2_zfmisc_1(B_21, D_23))=k2_zfmisc_1(k3_xboole_0(A_20, B_21), k3_xboole_0(C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.85/6.35  tff(c_42, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_7'), k2_zfmisc_1('#skF_5', '#skF_6'))!=k2_zfmisc_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.85/6.35  tff(c_47, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_5'), k3_xboole_0('#skF_7', '#skF_6'))!=k2_zfmisc_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 13.85/6.35  tff(c_49, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_5'), k3_xboole_0('#skF_6', '#skF_7'))!=k2_zfmisc_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47])).
% 13.85/6.35  tff(c_23761, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_6', '#skF_7'))!=k2_zfmisc_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23453, c_49])).
% 13.85/6.35  tff(c_39226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23036, c_23761])).
% 13.85/6.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.85/6.35  
% 13.85/6.35  Inference rules
% 13.85/6.35  ----------------------
% 13.85/6.35  #Ref     : 0
% 13.85/6.35  #Sup     : 9907
% 13.85/6.35  #Fact    : 0
% 13.85/6.35  #Define  : 0
% 13.85/6.35  #Split   : 3
% 13.85/6.35  #Chain   : 0
% 13.85/6.35  #Close   : 0
% 13.85/6.35  
% 13.85/6.35  Ordering : KBO
% 13.85/6.35  
% 13.85/6.35  Simplification rules
% 13.85/6.35  ----------------------
% 13.85/6.35  #Subsume      : 1875
% 13.85/6.35  #Demod        : 13488
% 13.85/6.35  #Tautology    : 4581
% 13.85/6.35  #SimpNegUnit  : 4
% 13.85/6.35  #BackRed      : 34
% 13.85/6.35  
% 13.85/6.35  #Partial instantiations: 0
% 13.85/6.35  #Strategies tried      : 1
% 13.85/6.35  
% 13.85/6.35  Timing (in seconds)
% 13.85/6.35  ----------------------
% 13.85/6.35  Preprocessing        : 0.31
% 13.85/6.35  Parsing              : 0.16
% 13.85/6.35  CNF conversion       : 0.02
% 13.85/6.35  Main loop            : 5.21
% 13.85/6.35  Inferencing          : 0.88
% 13.85/6.35  Reduction            : 2.90
% 13.85/6.35  Demodulation         : 2.60
% 13.85/6.35  BG Simplification    : 0.10
% 13.85/6.35  Subsumption          : 1.09
% 13.85/6.36  Abstraction          : 0.20
% 13.85/6.36  MUC search           : 0.00
% 13.85/6.36  Cooper               : 0.00
% 13.85/6.36  Total                : 5.56
% 13.85/6.36  Index Insertion      : 0.00
% 13.85/6.36  Index Deletion       : 0.00
% 13.85/6.36  Index Matching       : 0.00
% 13.85/6.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
