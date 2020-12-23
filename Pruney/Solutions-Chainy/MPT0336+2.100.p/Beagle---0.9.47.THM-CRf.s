%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 13.01s
% Output     : CNFRefutation 13.01s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 461 expanded)
%              Number of equality atoms :   34 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    ! [B_19,A_18] :
      ( r1_xboole_0(B_19,A_18)
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,(
    ! [B_47,A_46] :
      ( r1_xboole_0(B_47,A_46)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(resolution,[status(thm)],[c_106,c_44])).

tff(c_76,plain,(
    r1_xboole_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_81,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_81])).

tff(c_1169,plain,(
    ! [A_185,C_186,B_187] :
      ( ~ r1_xboole_0(A_185,C_186)
      | ~ r1_xboole_0(A_185,B_187)
      | r1_xboole_0(A_185,k2_xboole_0(B_187,C_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5298,plain,(
    ! [B_333,C_334,A_335] :
      ( r1_xboole_0(k2_xboole_0(B_333,C_334),A_335)
      | ~ r1_xboole_0(A_335,C_334)
      | ~ r1_xboole_0(A_335,B_333) ) ),
    inference(resolution,[status(thm)],[c_1169,c_44])).

tff(c_74,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_8','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5316,plain,
    ( ~ r1_xboole_0('#skF_9','#skF_10')
    | ~ r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_5298,c_74])).

tff(c_5339,plain,(
    ~ r1_xboole_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5316])).

tff(c_5350,plain,(
    k4_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_116,c_5339])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_176,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden('#skF_1'(A_64,B_65),B_65)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_154,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_6'(A_60,B_61),B_61)
      | r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8308,plain,(
    ! [A_406,A_407,B_408] :
      ( r2_hidden('#skF_6'(A_406,k3_xboole_0(A_407,B_408)),B_408)
      | r1_xboole_0(A_406,k3_xboole_0(A_407,B_408)) ) ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_6'(A_20,B_21),A_20)
      | r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_89,plain,(
    k4_xboole_0('#skF_10','#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_76,c_85])).

tff(c_243,plain,(
    ! [D_79,B_80,A_81] :
      ( ~ r2_hidden(D_79,B_80)
      | ~ r2_hidden(D_79,k4_xboole_0(A_81,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_265,plain,(
    ! [D_82] :
      ( ~ r2_hidden(D_82,'#skF_9')
      | ~ r2_hidden(D_82,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_243])).

tff(c_283,plain,(
    ! [B_21] :
      ( ~ r2_hidden('#skF_6'('#skF_10',B_21),'#skF_9')
      | r1_xboole_0('#skF_10',B_21) ) ),
    inference(resolution,[status(thm)],[c_50,c_265])).

tff(c_8413,plain,(
    ! [A_409] : r1_xboole_0('#skF_10',k3_xboole_0(A_409,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_8308,c_283])).

tff(c_66,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8462,plain,(
    ! [A_411] : k4_xboole_0('#skF_10',k3_xboole_0(A_411,'#skF_9')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8413,c_66])).

tff(c_78,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_369,plain,(
    ! [C_101,B_102,A_103] :
      ( r2_hidden(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_382,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_11',B_104)
      | ~ r1_tarski('#skF_10',B_104) ) ),
    inference(resolution,[status(thm)],[c_78,c_369])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_417,plain,(
    ! [B_13,A_12] :
      ( ~ r2_hidden('#skF_11',B_13)
      | ~ r1_tarski('#skF_10',k4_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_382,c_28])).

tff(c_8517,plain,(
    ! [A_411] :
      ( ~ r2_hidden('#skF_11',k3_xboole_0(A_411,'#skF_9'))
      | ~ r1_tarski('#skF_10','#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8462,c_417])).

tff(c_8562,plain,(
    ! [A_411] : ~ r2_hidden('#skF_11',k3_xboole_0(A_411,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_8517])).

tff(c_80,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_9'),k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_4'(A_12,B_13,C_14),A_12)
      | r2_hidden('#skF_5'(A_12,B_13,C_14),C_14)
      | k4_xboole_0(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2528,plain,(
    ! [A_243,B_244,C_245] :
      ( ~ r2_hidden('#skF_4'(A_243,B_244,C_245),B_244)
      | r2_hidden('#skF_5'(A_243,B_244,C_245),C_245)
      | k4_xboole_0(A_243,B_244) = C_245 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2775,plain,(
    ! [A_263,C_264] :
      ( r2_hidden('#skF_5'(A_263,A_263,C_264),C_264)
      | k4_xboole_0(A_263,A_263) = C_264 ) ),
    inference(resolution,[status(thm)],[c_42,c_2528])).

tff(c_54,plain,(
    ! [A_25,B_26,C_29] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_29,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2834,plain,(
    ! [A_265,B_266,A_267] :
      ( ~ r1_xboole_0(A_265,B_266)
      | k4_xboole_0(A_267,A_267) = k3_xboole_0(A_265,B_266) ) ),
    inference(resolution,[status(thm)],[c_2775,c_54])).

tff(c_2872,plain,(
    ! [A_267] : k4_xboole_0(A_267,A_267) = k3_xboole_0('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_84,c_2834])).

tff(c_2873,plain,(
    ! [A_267] : k4_xboole_0(A_267,A_267) = k3_xboole_0('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2834])).

tff(c_3092,plain,(
    k3_xboole_0('#skF_10','#skF_9') = k3_xboole_0('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2872,c_2873])).

tff(c_183,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_197,plain,(
    ! [A_67,B_68,B_2] :
      ( ~ r1_xboole_0(A_67,B_68)
      | r1_tarski(k3_xboole_0(A_67,B_68),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_3123,plain,(
    ! [B_2] :
      ( ~ r1_xboole_0('#skF_10','#skF_9')
      | r1_tarski(k3_xboole_0('#skF_9','#skF_10'),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3092,c_197])).

tff(c_3151,plain,(
    ! [B_2] : r1_tarski(k3_xboole_0('#skF_9','#skF_10'),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3123])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_6'(A_20,B_21),B_21)
      | r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_293,plain,(
    ! [A_87,B_88,A_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | r1_xboole_0(A_89,k3_xboole_0(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_48,c_183])).

tff(c_304,plain,(
    ! [A_89,A_87,B_88] :
      ( k4_xboole_0(A_89,k3_xboole_0(A_87,B_88)) = A_89
      | ~ r1_xboole_0(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_293,c_66])).

tff(c_3105,plain,(
    ! [A_89] :
      ( k4_xboole_0(A_89,k3_xboole_0('#skF_9','#skF_10')) = A_89
      | ~ r1_xboole_0('#skF_10','#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3092,c_304])).

tff(c_3141,plain,(
    ! [A_89] : k4_xboole_0(A_89,k3_xboole_0('#skF_9','#skF_10')) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3105])).

tff(c_3345,plain,(
    ! [A_279] : k4_xboole_0(A_279,k3_xboole_0('#skF_9','#skF_10')) = A_279 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3105])).

tff(c_56,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,k4_xboole_0(B_31,C_32))) = k4_xboole_0(A_30,C_32)
      | ~ r1_tarski(C_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3368,plain,(
    ! [A_30,A_279] :
      ( k2_xboole_0(k4_xboole_0(A_30,A_279),k3_xboole_0(A_30,A_279)) = k4_xboole_0(A_30,k3_xboole_0('#skF_9','#skF_10'))
      | ~ r1_tarski(k3_xboole_0('#skF_9','#skF_10'),A_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3345,c_56])).

tff(c_3426,plain,(
    ! [A_30,A_279] : k2_xboole_0(k4_xboole_0(A_30,A_279),k3_xboole_0(A_30,A_279)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_3141,c_3368])).

tff(c_72,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(k1_tarski(A_40),B_41) = k1_tarski(A_40)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1477,plain,(
    ! [A_198,B_199,C_200] :
      ( k2_xboole_0(k4_xboole_0(A_198,B_199),k3_xboole_0(A_198,k4_xboole_0(B_199,C_200))) = k4_xboole_0(A_198,C_200)
      | ~ r1_tarski(C_200,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1528,plain,(
    ! [A_198,B_41,A_40] :
      ( k4_xboole_0(A_198,B_41) = k2_xboole_0(k4_xboole_0(A_198,k1_tarski(A_40)),k3_xboole_0(A_198,k1_tarski(A_40)))
      | ~ r1_tarski(B_41,k1_tarski(A_40))
      | r2_hidden(A_40,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1477])).

tff(c_24330,plain,(
    ! [A_784,B_785,A_786] :
      ( k4_xboole_0(A_784,B_785) = A_784
      | ~ r1_tarski(B_785,k1_tarski(A_786))
      | r2_hidden(A_786,B_785) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3426,c_1528])).

tff(c_24353,plain,(
    ! [A_784] :
      ( k4_xboole_0(A_784,k3_xboole_0('#skF_8','#skF_9')) = A_784
      | r2_hidden('#skF_11',k3_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_80,c_24330])).

tff(c_24364,plain,(
    ! [A_787] : k4_xboole_0(A_787,k3_xboole_0('#skF_8','#skF_9')) = A_787 ),
    inference(negUnitSimplification,[status(thm)],[c_8562,c_24353])).

tff(c_165,plain,(
    ! [A_62,B_63] :
      ( ~ r1_xboole_0(k3_xboole_0(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_174,plain,(
    ! [A_62,A_46] :
      ( r1_xboole_0(A_62,A_46)
      | k4_xboole_0(A_46,k3_xboole_0(A_62,A_46)) != A_46 ) ),
    inference(resolution,[status(thm)],[c_116,c_165])).

tff(c_24902,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_24364,c_174])).

tff(c_24923,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_24902,c_66])).

tff(c_24932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5350,c_24923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.01/5.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.08  
% 13.01/5.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1
% 13.01/5.08  
% 13.01/5.08  %Foreground sorts:
% 13.01/5.08  
% 13.01/5.08  
% 13.01/5.08  %Background operators:
% 13.01/5.08  
% 13.01/5.08  
% 13.01/5.08  %Foreground operators:
% 13.01/5.08  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.01/5.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.01/5.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.01/5.08  tff('#skF_11', type, '#skF_11': $i).
% 13.01/5.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.01/5.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.01/5.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.01/5.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.01/5.08  tff('#skF_10', type, '#skF_10': $i).
% 13.01/5.08  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.01/5.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.01/5.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.01/5.08  tff('#skF_9', type, '#skF_9': $i).
% 13.01/5.08  tff('#skF_8', type, '#skF_8': $i).
% 13.01/5.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.01/5.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.01/5.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.01/5.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.01/5.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.01/5.09  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.01/5.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.01/5.09  
% 13.01/5.10  tff(f_117, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.01/5.10  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.01/5.10  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 13.01/5.10  tff(f_107, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 13.01/5.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.01/5.10  tff(f_73, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.01/5.10  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.01/5.10  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.01/5.10  tff(f_87, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 13.01/5.10  tff(f_91, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 13.01/5.10  tff(f_122, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 13.01/5.10  tff(f_113, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 13.01/5.10  tff(c_106, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k4_xboole_0(A_46, B_47)!=A_46)), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.01/5.10  tff(c_44, plain, (![B_19, A_18]: (r1_xboole_0(B_19, A_18) | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.10  tff(c_116, plain, (![B_47, A_46]: (r1_xboole_0(B_47, A_46) | k4_xboole_0(A_46, B_47)!=A_46)), inference(resolution, [status(thm)], [c_106, c_44])).
% 13.01/5.10  tff(c_76, plain, (r1_xboole_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.10  tff(c_81, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.10  tff(c_84, plain, (r1_xboole_0('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_76, c_81])).
% 13.01/5.10  tff(c_1169, plain, (![A_185, C_186, B_187]: (~r1_xboole_0(A_185, C_186) | ~r1_xboole_0(A_185, B_187) | r1_xboole_0(A_185, k2_xboole_0(B_187, C_186)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.01/5.10  tff(c_5298, plain, (![B_333, C_334, A_335]: (r1_xboole_0(k2_xboole_0(B_333, C_334), A_335) | ~r1_xboole_0(A_335, C_334) | ~r1_xboole_0(A_335, B_333))), inference(resolution, [status(thm)], [c_1169, c_44])).
% 13.01/5.10  tff(c_74, plain, (~r1_xboole_0(k2_xboole_0('#skF_8', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.10  tff(c_5316, plain, (~r1_xboole_0('#skF_9', '#skF_10') | ~r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_5298, c_74])).
% 13.01/5.10  tff(c_5339, plain, (~r1_xboole_0('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5316])).
% 13.01/5.10  tff(c_5350, plain, (k4_xboole_0('#skF_8', '#skF_9')!='#skF_8'), inference(resolution, [status(thm)], [c_116, c_5339])).
% 13.01/5.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.01/5.10  tff(c_176, plain, (![A_64, B_65]: (~r2_hidden('#skF_1'(A_64, B_65), B_65) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.01/5.10  tff(c_181, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_176])).
% 13.01/5.10  tff(c_154, plain, (![A_60, B_61]: (r2_hidden('#skF_6'(A_60, B_61), B_61) | r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.01/5.10  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.01/5.10  tff(c_8308, plain, (![A_406, A_407, B_408]: (r2_hidden('#skF_6'(A_406, k3_xboole_0(A_407, B_408)), B_408) | r1_xboole_0(A_406, k3_xboole_0(A_407, B_408)))), inference(resolution, [status(thm)], [c_154, c_10])).
% 13.01/5.10  tff(c_50, plain, (![A_20, B_21]: (r2_hidden('#skF_6'(A_20, B_21), A_20) | r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.01/5.10  tff(c_85, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.01/5.10  tff(c_89, plain, (k4_xboole_0('#skF_10', '#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_76, c_85])).
% 13.01/5.10  tff(c_243, plain, (![D_79, B_80, A_81]: (~r2_hidden(D_79, B_80) | ~r2_hidden(D_79, k4_xboole_0(A_81, B_80)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.10  tff(c_265, plain, (![D_82]: (~r2_hidden(D_82, '#skF_9') | ~r2_hidden(D_82, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_243])).
% 13.01/5.10  tff(c_283, plain, (![B_21]: (~r2_hidden('#skF_6'('#skF_10', B_21), '#skF_9') | r1_xboole_0('#skF_10', B_21))), inference(resolution, [status(thm)], [c_50, c_265])).
% 13.01/5.10  tff(c_8413, plain, (![A_409]: (r1_xboole_0('#skF_10', k3_xboole_0(A_409, '#skF_9')))), inference(resolution, [status(thm)], [c_8308, c_283])).
% 13.01/5.10  tff(c_66, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.01/5.10  tff(c_8462, plain, (![A_411]: (k4_xboole_0('#skF_10', k3_xboole_0(A_411, '#skF_9'))='#skF_10')), inference(resolution, [status(thm)], [c_8413, c_66])).
% 13.01/5.10  tff(c_78, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.10  tff(c_369, plain, (![C_101, B_102, A_103]: (r2_hidden(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.01/5.10  tff(c_382, plain, (![B_104]: (r2_hidden('#skF_11', B_104) | ~r1_tarski('#skF_10', B_104))), inference(resolution, [status(thm)], [c_78, c_369])).
% 13.01/5.10  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.10  tff(c_417, plain, (![B_13, A_12]: (~r2_hidden('#skF_11', B_13) | ~r1_tarski('#skF_10', k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_382, c_28])).
% 13.01/5.10  tff(c_8517, plain, (![A_411]: (~r2_hidden('#skF_11', k3_xboole_0(A_411, '#skF_9')) | ~r1_tarski('#skF_10', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8462, c_417])).
% 13.01/5.10  tff(c_8562, plain, (![A_411]: (~r2_hidden('#skF_11', k3_xboole_0(A_411, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_8517])).
% 13.01/5.10  tff(c_80, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_9'), k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.10  tff(c_42, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_4'(A_12, B_13, C_14), A_12) | r2_hidden('#skF_5'(A_12, B_13, C_14), C_14) | k4_xboole_0(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.10  tff(c_2528, plain, (![A_243, B_244, C_245]: (~r2_hidden('#skF_4'(A_243, B_244, C_245), B_244) | r2_hidden('#skF_5'(A_243, B_244, C_245), C_245) | k4_xboole_0(A_243, B_244)=C_245)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.10  tff(c_2775, plain, (![A_263, C_264]: (r2_hidden('#skF_5'(A_263, A_263, C_264), C_264) | k4_xboole_0(A_263, A_263)=C_264)), inference(resolution, [status(thm)], [c_42, c_2528])).
% 13.01/5.10  tff(c_54, plain, (![A_25, B_26, C_29]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_29, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.01/5.10  tff(c_2834, plain, (![A_265, B_266, A_267]: (~r1_xboole_0(A_265, B_266) | k4_xboole_0(A_267, A_267)=k3_xboole_0(A_265, B_266))), inference(resolution, [status(thm)], [c_2775, c_54])).
% 13.01/5.10  tff(c_2872, plain, (![A_267]: (k4_xboole_0(A_267, A_267)=k3_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_84, c_2834])).
% 13.01/5.10  tff(c_2873, plain, (![A_267]: (k4_xboole_0(A_267, A_267)=k3_xboole_0('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_2834])).
% 13.01/5.10  tff(c_3092, plain, (k3_xboole_0('#skF_10', '#skF_9')=k3_xboole_0('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2872, c_2873])).
% 13.01/5.10  tff(c_183, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.01/5.10  tff(c_197, plain, (![A_67, B_68, B_2]: (~r1_xboole_0(A_67, B_68) | r1_tarski(k3_xboole_0(A_67, B_68), B_2))), inference(resolution, [status(thm)], [c_6, c_183])).
% 13.01/5.10  tff(c_3123, plain, (![B_2]: (~r1_xboole_0('#skF_10', '#skF_9') | r1_tarski(k3_xboole_0('#skF_9', '#skF_10'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_3092, c_197])).
% 13.01/5.10  tff(c_3151, plain, (![B_2]: (r1_tarski(k3_xboole_0('#skF_9', '#skF_10'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3123])).
% 13.01/5.10  tff(c_48, plain, (![A_20, B_21]: (r2_hidden('#skF_6'(A_20, B_21), B_21) | r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.01/5.10  tff(c_293, plain, (![A_87, B_88, A_89]: (~r1_xboole_0(A_87, B_88) | r1_xboole_0(A_89, k3_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_48, c_183])).
% 13.01/5.10  tff(c_304, plain, (![A_89, A_87, B_88]: (k4_xboole_0(A_89, k3_xboole_0(A_87, B_88))=A_89 | ~r1_xboole_0(A_87, B_88))), inference(resolution, [status(thm)], [c_293, c_66])).
% 13.01/5.10  tff(c_3105, plain, (![A_89]: (k4_xboole_0(A_89, k3_xboole_0('#skF_9', '#skF_10'))=A_89 | ~r1_xboole_0('#skF_10', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3092, c_304])).
% 13.01/5.10  tff(c_3141, plain, (![A_89]: (k4_xboole_0(A_89, k3_xboole_0('#skF_9', '#skF_10'))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3105])).
% 13.01/5.10  tff(c_3345, plain, (![A_279]: (k4_xboole_0(A_279, k3_xboole_0('#skF_9', '#skF_10'))=A_279)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3105])).
% 13.01/5.10  tff(c_56, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))=k4_xboole_0(A_30, C_32) | ~r1_tarski(C_32, B_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.01/5.10  tff(c_3368, plain, (![A_30, A_279]: (k2_xboole_0(k4_xboole_0(A_30, A_279), k3_xboole_0(A_30, A_279))=k4_xboole_0(A_30, k3_xboole_0('#skF_9', '#skF_10')) | ~r1_tarski(k3_xboole_0('#skF_9', '#skF_10'), A_279))), inference(superposition, [status(thm), theory('equality')], [c_3345, c_56])).
% 13.01/5.10  tff(c_3426, plain, (![A_30, A_279]: (k2_xboole_0(k4_xboole_0(A_30, A_279), k3_xboole_0(A_30, A_279))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_3151, c_3141, c_3368])).
% 13.01/5.10  tff(c_72, plain, (![A_40, B_41]: (k4_xboole_0(k1_tarski(A_40), B_41)=k1_tarski(A_40) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.01/5.10  tff(c_1477, plain, (![A_198, B_199, C_200]: (k2_xboole_0(k4_xboole_0(A_198, B_199), k3_xboole_0(A_198, k4_xboole_0(B_199, C_200)))=k4_xboole_0(A_198, C_200) | ~r1_tarski(C_200, B_199))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.01/5.10  tff(c_1528, plain, (![A_198, B_41, A_40]: (k4_xboole_0(A_198, B_41)=k2_xboole_0(k4_xboole_0(A_198, k1_tarski(A_40)), k3_xboole_0(A_198, k1_tarski(A_40))) | ~r1_tarski(B_41, k1_tarski(A_40)) | r2_hidden(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1477])).
% 13.01/5.10  tff(c_24330, plain, (![A_784, B_785, A_786]: (k4_xboole_0(A_784, B_785)=A_784 | ~r1_tarski(B_785, k1_tarski(A_786)) | r2_hidden(A_786, B_785))), inference(demodulation, [status(thm), theory('equality')], [c_3426, c_1528])).
% 13.01/5.10  tff(c_24353, plain, (![A_784]: (k4_xboole_0(A_784, k3_xboole_0('#skF_8', '#skF_9'))=A_784 | r2_hidden('#skF_11', k3_xboole_0('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_80, c_24330])).
% 13.01/5.10  tff(c_24364, plain, (![A_787]: (k4_xboole_0(A_787, k3_xboole_0('#skF_8', '#skF_9'))=A_787)), inference(negUnitSimplification, [status(thm)], [c_8562, c_24353])).
% 13.01/5.10  tff(c_165, plain, (![A_62, B_63]: (~r1_xboole_0(k3_xboole_0(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.01/5.10  tff(c_174, plain, (![A_62, A_46]: (r1_xboole_0(A_62, A_46) | k4_xboole_0(A_46, k3_xboole_0(A_62, A_46))!=A_46)), inference(resolution, [status(thm)], [c_116, c_165])).
% 13.01/5.10  tff(c_24902, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_24364, c_174])).
% 13.01/5.10  tff(c_24923, plain, (k4_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_24902, c_66])).
% 13.01/5.10  tff(c_24932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5350, c_24923])).
% 13.01/5.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.10  
% 13.01/5.10  Inference rules
% 13.01/5.10  ----------------------
% 13.01/5.10  #Ref     : 2
% 13.01/5.10  #Sup     : 6087
% 13.01/5.10  #Fact    : 0
% 13.01/5.10  #Define  : 0
% 13.01/5.10  #Split   : 6
% 13.01/5.10  #Chain   : 0
% 13.01/5.10  #Close   : 0
% 13.01/5.10  
% 13.01/5.10  Ordering : KBO
% 13.01/5.10  
% 13.01/5.10  Simplification rules
% 13.01/5.10  ----------------------
% 13.01/5.10  #Subsume      : 1623
% 13.01/5.10  #Demod        : 2439
% 13.01/5.10  #Tautology    : 1924
% 13.01/5.11  #SimpNegUnit  : 74
% 13.01/5.11  #BackRed      : 7
% 13.01/5.11  
% 13.01/5.11  #Partial instantiations: 0
% 13.01/5.11  #Strategies tried      : 1
% 13.01/5.11  
% 13.01/5.11  Timing (in seconds)
% 13.01/5.11  ----------------------
% 13.01/5.11  Preprocessing        : 0.34
% 13.01/5.11  Parsing              : 0.18
% 13.01/5.11  CNF conversion       : 0.03
% 13.01/5.11  Main loop            : 3.98
% 13.01/5.11  Inferencing          : 0.94
% 13.01/5.11  Reduction            : 1.44
% 13.01/5.11  Demodulation         : 1.06
% 13.01/5.11  BG Simplification    : 0.10
% 13.01/5.11  Subsumption          : 1.22
% 13.01/5.11  Abstraction          : 0.13
% 13.01/5.11  MUC search           : 0.00
% 13.01/5.11  Cooper               : 0.00
% 13.01/5.11  Total                : 4.36
% 13.01/5.11  Index Insertion      : 0.00
% 13.01/5.11  Index Deletion       : 0.00
% 13.01/5.11  Index Matching       : 0.00
% 13.01/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
