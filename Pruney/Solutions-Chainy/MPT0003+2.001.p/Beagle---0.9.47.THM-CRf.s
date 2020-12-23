%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 292 expanded)
%              Number of leaves         :   25 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :  203 ( 587 expanded)
%              Number of equality atoms :   59 ( 116 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_46,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_48,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] :
                ~ ( r2_hidden(C,A)
                  & r2_hidden(C,B) ) )
        & ~ ( ? [C] :
                ( r2_hidden(C,A)
                & r2_hidden(C,B) )
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_32,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_246,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_2'(A_59,B_60,C_61),B_60)
      | r2_hidden('#skF_3'(A_59,B_60,C_61),C_61)
      | k3_xboole_0(A_59,B_60) = C_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_359,plain,(
    ! [B_68,A_69,C_70] :
      ( ~ v1_xboole_0(B_68)
      | r2_hidden('#skF_3'(A_69,B_68,C_70),C_70)
      | k3_xboole_0(A_69,B_68) = C_70 ) ),
    inference(resolution,[status(thm)],[c_246,c_2])).

tff(c_393,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ v1_xboole_0(B_72)
      | k3_xboole_0(A_73,B_72) = C_71 ) ),
    inference(resolution,[status(thm)],[c_359,c_2])).

tff(c_612,plain,(
    ! [B_81,A_82] :
      ( ~ v1_xboole_0(B_81)
      | k3_xboole_0(A_82,B_81) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32,c_393])).

tff(c_638,plain,(
    ! [A_82] : k3_xboole_0(A_82,k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_45,c_612])).

tff(c_421,plain,(
    ! [B_74,A_75] :
      ( ~ v1_xboole_0(B_74)
      | k3_xboole_0(A_75,B_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_45,c_393])).

tff(c_447,plain,(
    ! [A_75] : k3_xboole_0(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_421])).

tff(c_640,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_447])).

tff(c_66,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_74,plain,(
    k3_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_51])).

tff(c_720,plain,(
    k3_xboole_0('#skF_8','#skF_9') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [D_24,A_25,B_26] :
      ( r2_hidden(D_24,A_25)
      | ~ r2_hidden(D_24,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_25,B_26)),A_25)
      | v1_xboole_0(k3_xboole_0(A_25,B_26)) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_81,plain,(
    ! [D_27,B_28,A_29] :
      ( r2_hidden(D_27,B_28)
      | ~ r2_hidden(D_27,k3_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_34,B_35)),B_35)
      | v1_xboole_0(k3_xboole_0(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_36,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_7','#skF_6')
      | ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_158,plain,(
    ! [A_45] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_45,'#skF_9')),'#skF_8')
      | v1_xboole_0(k3_xboole_0(A_45,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_108,c_57])).

tff(c_163,plain,(
    v1_xboole_0(k3_xboole_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_158])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_813,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_2'(A_87,B_88,C_89),A_87)
      | r2_hidden('#skF_3'(A_87,B_88,C_89),C_89)
      | k3_xboole_0(A_87,B_88) = C_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1064,plain,(
    ! [B_92,C_93] :
      ( ~ r2_hidden('#skF_2'('#skF_9',B_92,C_93),'#skF_8')
      | r2_hidden('#skF_3'('#skF_9',B_92,C_93),C_93)
      | k3_xboole_0('#skF_9',B_92) = C_93 ) ),
    inference(resolution,[status(thm)],[c_813,c_57])).

tff(c_1177,plain,(
    ! [C_106] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8',C_106),C_106)
      | k3_xboole_0('#skF_9','#skF_8') = C_106 ) ),
    inference(resolution,[status(thm)],[c_22,c_1064])).

tff(c_1223,plain,(
    ! [C_107] :
      ( ~ v1_xboole_0(C_107)
      | k3_xboole_0('#skF_9','#skF_8') = C_107 ) ),
    inference(resolution,[status(thm)],[c_1177,c_2])).

tff(c_1256,plain,(
    k3_xboole_0('#skF_9','#skF_8') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_1223])).

tff(c_1222,plain,(
    ! [C_106] :
      ( ~ v1_xboole_0(C_106)
      | k3_xboole_0('#skF_9','#skF_8') = C_106 ) ),
    inference(resolution,[status(thm)],[c_1177,c_2])).

tff(c_1319,plain,(
    ! [C_108] :
      ( ~ v1_xboole_0(C_108)
      | C_108 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1222])).

tff(c_1331,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_163,c_1319])).

tff(c_1347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_1331])).

tff(c_1348,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1463,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_2'(A_136,B_137,C_138),A_136)
      | r2_hidden('#skF_3'(A_136,B_137,C_138),C_138)
      | k3_xboole_0(A_136,B_137) = C_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1499,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ v1_xboole_0(A_139)
      | r2_hidden('#skF_3'(A_139,B_140,C_141),C_141)
      | k3_xboole_0(A_139,B_140) = C_141 ) ),
    inference(resolution,[status(thm)],[c_1463,c_2])).

tff(c_1519,plain,(
    ! [C_142,A_143,B_144] :
      ( ~ v1_xboole_0(C_142)
      | ~ v1_xboole_0(A_143)
      | k3_xboole_0(A_143,B_144) = C_142 ) ),
    inference(resolution,[status(thm)],[c_1499,c_2])).

tff(c_1642,plain,(
    ! [A_151,B_152] :
      ( ~ v1_xboole_0(A_151)
      | k3_xboole_0(A_151,B_152) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32,c_1519])).

tff(c_1659,plain,(
    ! [B_152] : k3_xboole_0(k1_xboole_0,B_152) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_45,c_1642])).

tff(c_1538,plain,(
    ! [A_145,B_146] :
      ( ~ v1_xboole_0(A_145)
      | k3_xboole_0(A_145,B_146) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_45,c_1519])).

tff(c_1555,plain,(
    ! [B_146] : k3_xboole_0(k1_xboole_0,B_146) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_1538])).

tff(c_1661,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_1555])).

tff(c_1354,plain,(
    ! [A_111,B_112] :
      ( r1_xboole_0(A_111,B_112)
      | k3_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1362,plain,(
    k3_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1354,c_51])).

tff(c_1707,plain,(
    k3_xboole_0('#skF_8','#skF_9') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_1362])).

tff(c_24,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1717,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden('#skF_2'(A_154,B_155,C_156),B_155)
      | r2_hidden('#skF_3'(A_154,B_155,C_156),C_156)
      | k3_xboole_0(A_154,B_155) = C_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_7','#skF_5')
      | ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1369,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1988,plain,(
    ! [A_172,C_173] :
      ( ~ r2_hidden('#skF_2'(A_172,'#skF_9',C_173),'#skF_8')
      | r2_hidden('#skF_3'(A_172,'#skF_9',C_173),C_173)
      | k3_xboole_0(A_172,'#skF_9') = C_173 ) ),
    inference(resolution,[status(thm)],[c_1717,c_1369])).

tff(c_2154,plain,(
    ! [C_187] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_9',C_187),C_187)
      | k3_xboole_0('#skF_8','#skF_9') = C_187 ) ),
    inference(resolution,[status(thm)],[c_24,c_1988])).

tff(c_2190,plain,(
    ! [C_188] :
      ( ~ v1_xboole_0(C_188)
      | k3_xboole_0('#skF_8','#skF_9') = C_188 ) ),
    inference(resolution,[status(thm)],[c_2154,c_2])).

tff(c_2208,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_2190])).

tff(c_2218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1707,c_2208])).

tff(c_2219,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2413,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden('#skF_2'(A_223,B_224,C_225),A_223)
      | r2_hidden('#skF_3'(A_223,B_224,C_225),C_225)
      | k3_xboole_0(A_223,B_224) = C_225 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2504,plain,(
    ! [A_231,B_232,C_233] :
      ( ~ v1_xboole_0(A_231)
      | r2_hidden('#skF_3'(A_231,B_232,C_233),C_233)
      | k3_xboole_0(A_231,B_232) = C_233 ) ),
    inference(resolution,[status(thm)],[c_2413,c_2])).

tff(c_2539,plain,(
    ! [C_236,A_237,B_238] :
      ( ~ v1_xboole_0(C_236)
      | ~ v1_xboole_0(A_237)
      | k3_xboole_0(A_237,B_238) = C_236 ) ),
    inference(resolution,[status(thm)],[c_2504,c_2])).

tff(c_2801,plain,(
    ! [A_248,B_249] :
      ( ~ v1_xboole_0(A_248)
      | k3_xboole_0(A_248,B_249) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32,c_2539])).

tff(c_2833,plain,(
    ! [B_249] : k3_xboole_0(k1_xboole_0,B_249) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_45,c_2801])).

tff(c_2567,plain,(
    ! [A_239,B_240] :
      ( ~ v1_xboole_0(A_239)
      | k3_xboole_0(A_239,B_240) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_45,c_2539])).

tff(c_2593,plain,(
    ! [B_240] : k3_xboole_0(k1_xboole_0,B_240) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_2567])).

tff(c_2835,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2593])).

tff(c_2928,plain,(
    k3_xboole_0('#skF_8','#skF_9') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_1362])).

tff(c_3029,plain,(
    ! [A_252,B_253,C_254] :
      ( r2_hidden('#skF_2'(A_252,B_253,C_254),B_253)
      | r2_hidden('#skF_3'(A_252,B_253,C_254),C_254)
      | k3_xboole_0(A_252,B_253) = C_254 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [C_15] :
      ( r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2230,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_9')
      | ~ r2_hidden(C_15,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_3104,plain,(
    ! [A_255,C_256] :
      ( ~ r2_hidden('#skF_2'(A_255,'#skF_9',C_256),'#skF_8')
      | r2_hidden('#skF_3'(A_255,'#skF_9',C_256),C_256)
      | k3_xboole_0(A_255,'#skF_9') = C_256 ) ),
    inference(resolution,[status(thm)],[c_3029,c_2230])).

tff(c_3235,plain,(
    ! [C_261] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_9',C_261),C_261)
      | k3_xboole_0('#skF_8','#skF_9') = C_261 ) ),
    inference(resolution,[status(thm)],[c_24,c_3104])).

tff(c_3273,plain,(
    ! [C_262] :
      ( ~ v1_xboole_0(C_262)
      | k3_xboole_0('#skF_8','#skF_9') = C_262 ) ),
    inference(resolution,[status(thm)],[c_3235,c_2])).

tff(c_3303,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_3273])).

tff(c_3317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2928,c_3303])).

tff(c_3318,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3322,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3318,c_26])).

tff(c_3347,plain,(
    ! [D_265,A_266,B_267] :
      ( r2_hidden(D_265,k3_xboole_0(A_266,B_267))
      | ~ r2_hidden(D_265,B_267)
      | ~ r2_hidden(D_265,A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3363,plain,(
    ! [D_268] :
      ( r2_hidden(D_268,k1_xboole_0)
      | ~ r2_hidden(D_268,'#skF_6')
      | ~ r2_hidden(D_268,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3322,c_3347])).

tff(c_3372,plain,(
    ! [D_268] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_268,'#skF_6')
      | ~ r2_hidden(D_268,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3363,c_2])).

tff(c_3378,plain,(
    ! [D_269] :
      ( ~ r2_hidden(D_269,'#skF_6')
      | ~ r2_hidden(D_269,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_3372])).

tff(c_3381,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_2219,c_3378])).

tff(c_3389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_3381])).

tff(c_3391,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3396,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_3398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3391,c_3396])).

tff(c_3399,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3390,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3412,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3391,c_40])).

tff(c_3413,plain,(
    ! [A_271,B_272] :
      ( k3_xboole_0(A_271,B_272) = k1_xboole_0
      | ~ r1_xboole_0(A_271,B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3420,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3412,c_3413])).

tff(c_3542,plain,(
    ! [D_289,A_290,B_291] :
      ( r2_hidden(D_289,k3_xboole_0(A_290,B_291))
      | ~ r2_hidden(D_289,B_291)
      | ~ r2_hidden(D_289,A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3596,plain,(
    ! [D_294] :
      ( r2_hidden(D_294,k1_xboole_0)
      | ~ r2_hidden(D_294,'#skF_6')
      | ~ r2_hidden(D_294,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3420,c_3542])).

tff(c_3611,plain,(
    ! [D_294] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_294,'#skF_6')
      | ~ r2_hidden(D_294,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3596,c_2])).

tff(c_3619,plain,(
    ! [D_295] :
      ( ~ r2_hidden(D_295,'#skF_6')
      | ~ r2_hidden(D_295,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_3611])).

tff(c_3630,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3390,c_3619])).

tff(c_3638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_3630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.75  
% 4.02/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.76  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 4.02/1.76  
% 4.02/1.76  %Foreground sorts:
% 4.02/1.76  
% 4.02/1.76  
% 4.02/1.76  %Background operators:
% 4.02/1.76  
% 4.02/1.76  
% 4.02/1.76  %Foreground operators:
% 4.02/1.76  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.02/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.02/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.02/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.02/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.02/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.02/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.02/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.02/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.02/1.76  tff('#skF_9', type, '#skF_9': $i).
% 4.02/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.02/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.02/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.02/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.02/1.76  
% 4.02/1.78  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_xboole_0)).
% 4.02/1.78  tff(f_46, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 4.02/1.78  tff(f_48, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.02/1.78  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.02/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.02/1.78  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.02/1.78  tff(f_67, negated_conjecture, ~(![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.02/1.78  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.78  tff(c_30, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.02/1.78  tff(c_45, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 4.02/1.78  tff(c_32, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.02/1.78  tff(c_246, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_2'(A_59, B_60, C_61), B_60) | r2_hidden('#skF_3'(A_59, B_60, C_61), C_61) | k3_xboole_0(A_59, B_60)=C_61)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.78  tff(c_359, plain, (![B_68, A_69, C_70]: (~v1_xboole_0(B_68) | r2_hidden('#skF_3'(A_69, B_68, C_70), C_70) | k3_xboole_0(A_69, B_68)=C_70)), inference(resolution, [status(thm)], [c_246, c_2])).
% 4.02/1.78  tff(c_393, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~v1_xboole_0(B_72) | k3_xboole_0(A_73, B_72)=C_71)), inference(resolution, [status(thm)], [c_359, c_2])).
% 4.02/1.78  tff(c_612, plain, (![B_81, A_82]: (~v1_xboole_0(B_81) | k3_xboole_0(A_82, B_81)='#skF_4')), inference(resolution, [status(thm)], [c_32, c_393])).
% 4.02/1.78  tff(c_638, plain, (![A_82]: (k3_xboole_0(A_82, k1_xboole_0)='#skF_4')), inference(resolution, [status(thm)], [c_45, c_612])).
% 4.02/1.78  tff(c_421, plain, (![B_74, A_75]: (~v1_xboole_0(B_74) | k3_xboole_0(A_75, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_393])).
% 4.02/1.78  tff(c_447, plain, (![A_75]: (k3_xboole_0(A_75, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_421])).
% 4.02/1.78  tff(c_640, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_638, c_447])).
% 4.02/1.78  tff(c_66, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.78  tff(c_44, plain, (r2_hidden('#skF_7', '#skF_5') | ~r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_51, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_44])).
% 4.02/1.78  tff(c_74, plain, (k3_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_51])).
% 4.02/1.78  tff(c_720, plain, (k3_xboole_0('#skF_8', '#skF_9')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_74])).
% 4.02/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.78  tff(c_75, plain, (![D_24, A_25, B_26]: (r2_hidden(D_24, A_25) | ~r2_hidden(D_24, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_80, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(k3_xboole_0(A_25, B_26)), A_25) | v1_xboole_0(k3_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_4, c_75])).
% 4.02/1.78  tff(c_81, plain, (![D_27, B_28, A_29]: (r2_hidden(D_27, B_28) | ~r2_hidden(D_27, k3_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_108, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(k3_xboole_0(A_34, B_35)), B_35) | v1_xboole_0(k3_xboole_0(A_34, B_35)))), inference(resolution, [status(thm)], [c_4, c_81])).
% 4.02/1.78  tff(c_36, plain, (![C_15]: (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_57, plain, (![C_15]: (~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(splitLeft, [status(thm)], [c_36])).
% 4.02/1.78  tff(c_158, plain, (![A_45]: (~r2_hidden('#skF_1'(k3_xboole_0(A_45, '#skF_9')), '#skF_8') | v1_xboole_0(k3_xboole_0(A_45, '#skF_9')))), inference(resolution, [status(thm)], [c_108, c_57])).
% 4.02/1.78  tff(c_163, plain, (v1_xboole_0(k3_xboole_0('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_80, c_158])).
% 4.02/1.78  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_813, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_2'(A_87, B_88, C_89), A_87) | r2_hidden('#skF_3'(A_87, B_88, C_89), C_89) | k3_xboole_0(A_87, B_88)=C_89)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_1064, plain, (![B_92, C_93]: (~r2_hidden('#skF_2'('#skF_9', B_92, C_93), '#skF_8') | r2_hidden('#skF_3'('#skF_9', B_92, C_93), C_93) | k3_xboole_0('#skF_9', B_92)=C_93)), inference(resolution, [status(thm)], [c_813, c_57])).
% 4.02/1.78  tff(c_1177, plain, (![C_106]: (r2_hidden('#skF_3'('#skF_9', '#skF_8', C_106), C_106) | k3_xboole_0('#skF_9', '#skF_8')=C_106)), inference(resolution, [status(thm)], [c_22, c_1064])).
% 4.02/1.78  tff(c_1223, plain, (![C_107]: (~v1_xboole_0(C_107) | k3_xboole_0('#skF_9', '#skF_8')=C_107)), inference(resolution, [status(thm)], [c_1177, c_2])).
% 4.02/1.78  tff(c_1256, plain, (k3_xboole_0('#skF_9', '#skF_8')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_1223])).
% 4.02/1.78  tff(c_1222, plain, (![C_106]: (~v1_xboole_0(C_106) | k3_xboole_0('#skF_9', '#skF_8')=C_106)), inference(resolution, [status(thm)], [c_1177, c_2])).
% 4.02/1.78  tff(c_1319, plain, (![C_108]: (~v1_xboole_0(C_108) | C_108='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1222])).
% 4.02/1.78  tff(c_1331, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_4'), inference(resolution, [status(thm)], [c_163, c_1319])).
% 4.02/1.78  tff(c_1347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_1331])).
% 4.02/1.78  tff(c_1348, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 4.02/1.78  tff(c_1463, plain, (![A_136, B_137, C_138]: (r2_hidden('#skF_2'(A_136, B_137, C_138), A_136) | r2_hidden('#skF_3'(A_136, B_137, C_138), C_138) | k3_xboole_0(A_136, B_137)=C_138)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_1499, plain, (![A_139, B_140, C_141]: (~v1_xboole_0(A_139) | r2_hidden('#skF_3'(A_139, B_140, C_141), C_141) | k3_xboole_0(A_139, B_140)=C_141)), inference(resolution, [status(thm)], [c_1463, c_2])).
% 4.02/1.78  tff(c_1519, plain, (![C_142, A_143, B_144]: (~v1_xboole_0(C_142) | ~v1_xboole_0(A_143) | k3_xboole_0(A_143, B_144)=C_142)), inference(resolution, [status(thm)], [c_1499, c_2])).
% 4.02/1.78  tff(c_1642, plain, (![A_151, B_152]: (~v1_xboole_0(A_151) | k3_xboole_0(A_151, B_152)='#skF_4')), inference(resolution, [status(thm)], [c_32, c_1519])).
% 4.02/1.78  tff(c_1659, plain, (![B_152]: (k3_xboole_0(k1_xboole_0, B_152)='#skF_4')), inference(resolution, [status(thm)], [c_45, c_1642])).
% 4.02/1.78  tff(c_1538, plain, (![A_145, B_146]: (~v1_xboole_0(A_145) | k3_xboole_0(A_145, B_146)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_1519])).
% 4.02/1.78  tff(c_1555, plain, (![B_146]: (k3_xboole_0(k1_xboole_0, B_146)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_1538])).
% 4.02/1.78  tff(c_1661, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_1555])).
% 4.02/1.78  tff(c_1354, plain, (![A_111, B_112]: (r1_xboole_0(A_111, B_112) | k3_xboole_0(A_111, B_112)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.78  tff(c_1362, plain, (k3_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1354, c_51])).
% 4.02/1.78  tff(c_1707, plain, (k3_xboole_0('#skF_8', '#skF_9')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1661, c_1362])).
% 4.02/1.78  tff(c_24, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_1717, plain, (![A_154, B_155, C_156]: (r2_hidden('#skF_2'(A_154, B_155, C_156), B_155) | r2_hidden('#skF_3'(A_154, B_155, C_156), C_156) | k3_xboole_0(A_154, B_155)=C_156)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_38, plain, (![C_15]: (r2_hidden('#skF_7', '#skF_5') | ~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_1369, plain, (![C_15]: (~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.02/1.78  tff(c_1988, plain, (![A_172, C_173]: (~r2_hidden('#skF_2'(A_172, '#skF_9', C_173), '#skF_8') | r2_hidden('#skF_3'(A_172, '#skF_9', C_173), C_173) | k3_xboole_0(A_172, '#skF_9')=C_173)), inference(resolution, [status(thm)], [c_1717, c_1369])).
% 4.02/1.78  tff(c_2154, plain, (![C_187]: (r2_hidden('#skF_3'('#skF_8', '#skF_9', C_187), C_187) | k3_xboole_0('#skF_8', '#skF_9')=C_187)), inference(resolution, [status(thm)], [c_24, c_1988])).
% 4.02/1.78  tff(c_2190, plain, (![C_188]: (~v1_xboole_0(C_188) | k3_xboole_0('#skF_8', '#skF_9')=C_188)), inference(resolution, [status(thm)], [c_2154, c_2])).
% 4.02/1.78  tff(c_2208, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_2190])).
% 4.02/1.78  tff(c_2218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1707, c_2208])).
% 4.02/1.78  tff(c_2219, plain, (r2_hidden('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.02/1.78  tff(c_2413, plain, (![A_223, B_224, C_225]: (r2_hidden('#skF_2'(A_223, B_224, C_225), A_223) | r2_hidden('#skF_3'(A_223, B_224, C_225), C_225) | k3_xboole_0(A_223, B_224)=C_225)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_2504, plain, (![A_231, B_232, C_233]: (~v1_xboole_0(A_231) | r2_hidden('#skF_3'(A_231, B_232, C_233), C_233) | k3_xboole_0(A_231, B_232)=C_233)), inference(resolution, [status(thm)], [c_2413, c_2])).
% 4.02/1.78  tff(c_2539, plain, (![C_236, A_237, B_238]: (~v1_xboole_0(C_236) | ~v1_xboole_0(A_237) | k3_xboole_0(A_237, B_238)=C_236)), inference(resolution, [status(thm)], [c_2504, c_2])).
% 4.02/1.78  tff(c_2801, plain, (![A_248, B_249]: (~v1_xboole_0(A_248) | k3_xboole_0(A_248, B_249)='#skF_4')), inference(resolution, [status(thm)], [c_32, c_2539])).
% 4.02/1.78  tff(c_2833, plain, (![B_249]: (k3_xboole_0(k1_xboole_0, B_249)='#skF_4')), inference(resolution, [status(thm)], [c_45, c_2801])).
% 4.02/1.78  tff(c_2567, plain, (![A_239, B_240]: (~v1_xboole_0(A_239) | k3_xboole_0(A_239, B_240)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_2539])).
% 4.02/1.78  tff(c_2593, plain, (![B_240]: (k3_xboole_0(k1_xboole_0, B_240)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_2567])).
% 4.02/1.78  tff(c_2835, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2593])).
% 4.02/1.78  tff(c_2928, plain, (k3_xboole_0('#skF_8', '#skF_9')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2835, c_1362])).
% 4.02/1.78  tff(c_3029, plain, (![A_252, B_253, C_254]: (r2_hidden('#skF_2'(A_252, B_253, C_254), B_253) | r2_hidden('#skF_3'(A_252, B_253, C_254), C_254) | k3_xboole_0(A_252, B_253)=C_254)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_34, plain, (![C_15]: (r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_2230, plain, (![C_15]: (~r2_hidden(C_15, '#skF_9') | ~r2_hidden(C_15, '#skF_8'))), inference(splitLeft, [status(thm)], [c_34])).
% 4.02/1.78  tff(c_3104, plain, (![A_255, C_256]: (~r2_hidden('#skF_2'(A_255, '#skF_9', C_256), '#skF_8') | r2_hidden('#skF_3'(A_255, '#skF_9', C_256), C_256) | k3_xboole_0(A_255, '#skF_9')=C_256)), inference(resolution, [status(thm)], [c_3029, c_2230])).
% 4.02/1.78  tff(c_3235, plain, (![C_261]: (r2_hidden('#skF_3'('#skF_8', '#skF_9', C_261), C_261) | k3_xboole_0('#skF_8', '#skF_9')=C_261)), inference(resolution, [status(thm)], [c_24, c_3104])).
% 4.02/1.78  tff(c_3273, plain, (![C_262]: (~v1_xboole_0(C_262) | k3_xboole_0('#skF_8', '#skF_9')=C_262)), inference(resolution, [status(thm)], [c_3235, c_2])).
% 4.02/1.78  tff(c_3303, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_3273])).
% 4.02/1.78  tff(c_3317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2928, c_3303])).
% 4.02/1.78  tff(c_3318, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 4.02/1.78  tff(c_26, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.78  tff(c_3322, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_3318, c_26])).
% 4.02/1.78  tff(c_3347, plain, (![D_265, A_266, B_267]: (r2_hidden(D_265, k3_xboole_0(A_266, B_267)) | ~r2_hidden(D_265, B_267) | ~r2_hidden(D_265, A_266))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_3363, plain, (![D_268]: (r2_hidden(D_268, k1_xboole_0) | ~r2_hidden(D_268, '#skF_6') | ~r2_hidden(D_268, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3322, c_3347])).
% 4.02/1.78  tff(c_3372, plain, (![D_268]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_268, '#skF_6') | ~r2_hidden(D_268, '#skF_5'))), inference(resolution, [status(thm)], [c_3363, c_2])).
% 4.02/1.78  tff(c_3378, plain, (![D_269]: (~r2_hidden(D_269, '#skF_6') | ~r2_hidden(D_269, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_3372])).
% 4.02/1.78  tff(c_3381, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_2219, c_3378])).
% 4.02/1.78  tff(c_3389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1348, c_3381])).
% 4.02/1.78  tff(c_3391, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_44])).
% 4.02/1.78  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_6') | ~r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_3396, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_42])).
% 4.02/1.78  tff(c_3398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3391, c_3396])).
% 4.02/1.78  tff(c_3399, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 4.02/1.78  tff(c_3390, plain, (r2_hidden('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 4.02/1.78  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.78  tff(c_3412, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3391, c_40])).
% 4.02/1.78  tff(c_3413, plain, (![A_271, B_272]: (k3_xboole_0(A_271, B_272)=k1_xboole_0 | ~r1_xboole_0(A_271, B_272))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.78  tff(c_3420, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_3412, c_3413])).
% 4.02/1.78  tff(c_3542, plain, (![D_289, A_290, B_291]: (r2_hidden(D_289, k3_xboole_0(A_290, B_291)) | ~r2_hidden(D_289, B_291) | ~r2_hidden(D_289, A_290))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.78  tff(c_3596, plain, (![D_294]: (r2_hidden(D_294, k1_xboole_0) | ~r2_hidden(D_294, '#skF_6') | ~r2_hidden(D_294, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3420, c_3542])).
% 4.02/1.78  tff(c_3611, plain, (![D_294]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_294, '#skF_6') | ~r2_hidden(D_294, '#skF_5'))), inference(resolution, [status(thm)], [c_3596, c_2])).
% 4.02/1.78  tff(c_3619, plain, (![D_295]: (~r2_hidden(D_295, '#skF_6') | ~r2_hidden(D_295, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_3611])).
% 4.02/1.78  tff(c_3630, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3390, c_3619])).
% 4.02/1.78  tff(c_3638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3399, c_3630])).
% 4.02/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.78  
% 4.02/1.78  Inference rules
% 4.02/1.78  ----------------------
% 4.02/1.78  #Ref     : 0
% 4.02/1.78  #Sup     : 843
% 4.02/1.78  #Fact    : 0
% 4.02/1.78  #Define  : 0
% 4.02/1.78  #Split   : 9
% 4.02/1.78  #Chain   : 0
% 4.02/1.78  #Close   : 0
% 4.02/1.78  
% 4.02/1.78  Ordering : KBO
% 4.02/1.78  
% 4.02/1.78  Simplification rules
% 4.02/1.78  ----------------------
% 4.02/1.78  #Subsume      : 76
% 4.02/1.78  #Demod        : 485
% 4.02/1.78  #Tautology    : 322
% 4.02/1.78  #SimpNegUnit  : 6
% 4.02/1.78  #BackRed      : 33
% 4.02/1.78  
% 4.02/1.78  #Partial instantiations: 0
% 4.02/1.78  #Strategies tried      : 1
% 4.02/1.78  
% 4.02/1.78  Timing (in seconds)
% 4.02/1.78  ----------------------
% 4.47/1.78  Preprocessing        : 0.29
% 4.47/1.78  Parsing              : 0.15
% 4.47/1.78  CNF conversion       : 0.02
% 4.47/1.78  Main loop            : 0.71
% 4.47/1.78  Inferencing          : 0.26
% 4.47/1.78  Reduction            : 0.21
% 4.47/1.78  Demodulation         : 0.15
% 4.47/1.78  BG Simplification    : 0.04
% 4.47/1.78  Subsumption          : 0.14
% 4.47/1.78  Abstraction          : 0.04
% 4.47/1.78  MUC search           : 0.00
% 4.47/1.78  Cooper               : 0.00
% 4.47/1.78  Total                : 1.05
% 4.47/1.78  Index Insertion      : 0.00
% 4.47/1.78  Index Deletion       : 0.00
% 4.47/1.78  Index Matching       : 0.00
% 4.47/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
