%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 384 expanded)
%              Number of leaves         :   41 ( 143 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 721 expanded)
%              Number of equality atoms :   34 ( 132 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_17 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_4 > #skF_16 > #skF_14 > #skF_5 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_90,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_140,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_96,plain,(
    v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_178,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_96,c_169])).

tff(c_74,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_328,plain,(
    ! [A_73,B_74] :
      ( r1_xboole_0(A_73,B_74)
      | k3_xboole_0(A_73,B_74) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74])).

tff(c_162,plain,
    ( r2_hidden('#skF_16','#skF_14')
    | ~ r1_xboole_0('#skF_17','#skF_18') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_209,plain,(
    ~ r1_xboole_0('#skF_17','#skF_18') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_335,plain,(
    k3_xboole_0('#skF_17','#skF_18') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_328,c_209])).

tff(c_6,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | r2_hidden('#skF_1'(A_9),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4050,plain,(
    ! [D_303,B_304,A_305] :
      ( r2_hidden(D_303,B_304)
      | ~ r2_hidden(D_303,k3_xboole_0(A_305,B_304)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4064,plain,(
    ! [A_305,B_304] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_305,B_304)),B_304)
      | v1_xboole_0(k3_xboole_0(A_305,B_304)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4050])).

tff(c_5583,plain,(
    ! [A_435,B_436] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_435,B_436)),B_436)
      | v1_xboole_0(k3_xboole_0(A_435,B_436)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4050])).

tff(c_156,plain,(
    ! [C_54] :
      ( r2_hidden('#skF_16','#skF_14')
      | ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4942,plain,(
    ! [C_54] :
      ( ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_5834,plain,(
    ! [A_446] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_446,'#skF_18')),'#skF_17')
      | v1_xboole_0(k3_xboole_0(A_446,'#skF_18')) ) ),
    inference(resolution,[status(thm)],[c_5583,c_4942])).

tff(c_6150,plain,(
    ! [B_462] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_18',B_462)),'#skF_17')
      | v1_xboole_0(k3_xboole_0(B_462,'#skF_18')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5834])).

tff(c_6166,plain,
    ( v1_xboole_0(k3_xboole_0('#skF_17','#skF_18'))
    | v1_xboole_0(k3_xboole_0('#skF_18','#skF_17')) ),
    inference(resolution,[status(thm)],[c_4064,c_6150])).

tff(c_6183,plain,
    ( v1_xboole_0(k3_xboole_0('#skF_17','#skF_18'))
    | v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6166])).

tff(c_6185,plain,(
    v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_6183])).

tff(c_94,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_188,plain,(
    ! [A_39] :
      ( A_39 = '#skF_8'
      | ~ v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_94])).

tff(c_6192,plain,(
    k3_xboole_0('#skF_17','#skF_18') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6185,c_188])).

tff(c_6198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_6192])).

tff(c_6200,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_6183])).

tff(c_6199,plain,(
    v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_6183])).

tff(c_6333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6200,c_6199])).

tff(c_6334,plain,(
    r2_hidden('#skF_16','#skF_14') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_394,plain,(
    ! [D_89,A_90,B_91] :
      ( r2_hidden(D_89,A_90)
      | ~ r2_hidden(D_89,k4_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_736,plain,(
    ! [A_136,B_137] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_136,B_137)),A_136)
      | v1_xboole_0(k4_xboole_0(A_136,B_137)) ) ),
    inference(resolution,[status(thm)],[c_12,c_394])).

tff(c_10,plain,(
    ! [B_12,A_9] :
      ( ~ r2_hidden(B_12,A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_784,plain,(
    ! [A_138,B_139] :
      ( ~ v1_xboole_0(A_138)
      | v1_xboole_0(k4_xboole_0(A_138,B_139)) ) ),
    inference(resolution,[status(thm)],[c_736,c_10])).

tff(c_789,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = '#skF_8'
      | ~ v1_xboole_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_784,c_188])).

tff(c_795,plain,(
    ! [B_141] : k4_xboole_0('#skF_8',B_141) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_96,c_789])).

tff(c_493,plain,(
    ! [A_110,B_111] : k2_xboole_0(k4_xboole_0(A_110,B_111),k4_xboole_0(B_111,A_110)) = k5_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,(
    ! [A_35] : k2_xboole_0(A_35,A_35) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_522,plain,(
    ! [B_111] : k5_xboole_0(B_111,B_111) = k4_xboole_0(B_111,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_90])).

tff(c_50,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden('#skF_4'(A_19,B_20,C_21),A_19)
      | r2_hidden('#skF_5'(A_19,B_20,C_21),C_21)
      | k3_xboole_0(A_19,B_20) = C_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3083,plain,(
    ! [A_263,B_264,C_265] :
      ( r2_hidden('#skF_4'(A_263,B_264,C_265),B_264)
      | r2_hidden('#skF_5'(A_263,B_264,C_265),C_265)
      | k3_xboole_0(A_263,B_264) = C_265 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_154,plain,(
    ! [C_54] :
      ( r2_hidden('#skF_16','#skF_15')
      | ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_386,plain,(
    ! [C_54] :
      ( ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_3468,plain,(
    ! [A_275,C_276] :
      ( ~ r2_hidden('#skF_4'(A_275,'#skF_18',C_276),'#skF_17')
      | r2_hidden('#skF_5'(A_275,'#skF_18',C_276),C_276)
      | k3_xboole_0(A_275,'#skF_18') = C_276 ) ),
    inference(resolution,[status(thm)],[c_3083,c_386])).

tff(c_3922,plain,(
    ! [C_292] :
      ( r2_hidden('#skF_5'('#skF_17','#skF_18',C_292),C_292)
      | k3_xboole_0('#skF_17','#skF_18') = C_292 ) ),
    inference(resolution,[status(thm)],[c_50,c_3468])).

tff(c_820,plain,(
    ! [B_145] : k4_xboole_0('#skF_8',B_145) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_96,c_789])).

tff(c_342,plain,(
    ! [D_77,A_78,B_79] :
      ( ~ r2_hidden(D_77,A_78)
      | r2_hidden(D_77,k2_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_358,plain,(
    ! [A_78,B_79,D_77] :
      ( ~ v1_xboole_0(k2_xboole_0(A_78,B_79))
      | ~ r2_hidden(D_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_342,c_10])).

tff(c_509,plain,(
    ! [A_110,B_111,D_77] :
      ( ~ v1_xboole_0(k5_xboole_0(A_110,B_111))
      | ~ r2_hidden(D_77,k4_xboole_0(A_110,B_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_358])).

tff(c_840,plain,(
    ! [B_145,D_77] :
      ( ~ v1_xboole_0(k5_xboole_0('#skF_8',B_145))
      | ~ r2_hidden(D_77,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_509])).

tff(c_904,plain,(
    ! [D_77] : ~ r2_hidden(D_77,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_3938,plain,(
    k3_xboole_0('#skF_17','#skF_18') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3922,c_904])).

tff(c_3986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_3938])).

tff(c_3988,plain,(
    ! [B_293] : ~ v1_xboole_0(k5_xboole_0('#skF_8',B_293)) ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_3992,plain,(
    ~ v1_xboole_0(k4_xboole_0('#skF_8','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_3988])).

tff(c_4003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_795,c_3992])).

tff(c_4004,plain,(
    r2_hidden('#skF_16','#skF_15') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_4275,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_337,B_338)),B_338)
      | v1_xboole_0(k3_xboole_0(A_337,B_338)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4050])).

tff(c_152,plain,(
    ! [C_54] :
      ( r1_xboole_0('#skF_14','#skF_15')
      | ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4065,plain,(
    ! [C_54] :
      ( ~ r2_hidden(C_54,'#skF_18')
      | ~ r2_hidden(C_54,'#skF_17') ) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_4433,plain,(
    ! [A_347] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_347,'#skF_18')),'#skF_17')
      | v1_xboole_0(k3_xboole_0(A_347,'#skF_18')) ) ),
    inference(resolution,[status(thm)],[c_4275,c_4065])).

tff(c_4584,plain,(
    ! [B_356] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_18',B_356)),'#skF_17')
      | v1_xboole_0(k3_xboole_0(B_356,'#skF_18')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4433])).

tff(c_4592,plain,
    ( v1_xboole_0(k3_xboole_0('#skF_17','#skF_18'))
    | v1_xboole_0(k3_xboole_0('#skF_18','#skF_17')) ),
    inference(resolution,[status(thm)],[c_4064,c_4584])).

tff(c_4607,plain,
    ( v1_xboole_0(k3_xboole_0('#skF_17','#skF_18'))
    | v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4592])).

tff(c_4822,plain,(
    v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_4607])).

tff(c_4857,plain,(
    k3_xboole_0('#skF_17','#skF_18') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4822,c_188])).

tff(c_4863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_4857])).

tff(c_4865,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_4607])).

tff(c_4864,plain,(
    v1_xboole_0(k3_xboole_0('#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_4607])).

tff(c_4874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4865,c_4864])).

tff(c_4875,plain,(
    r1_xboole_0('#skF_14','#skF_15') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_336,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = '#skF_8'
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_72])).

tff(c_4881,plain,(
    k3_xboole_0('#skF_14','#skF_15') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4875,c_336])).

tff(c_7382,plain,(
    ! [D_541,A_542,B_543] :
      ( r2_hidden(D_541,k3_xboole_0(A_542,B_543))
      | ~ r2_hidden(D_541,B_543)
      | ~ r2_hidden(D_541,A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7590,plain,(
    ! [D_547] :
      ( r2_hidden(D_547,'#skF_8')
      | ~ r2_hidden(D_547,'#skF_15')
      | ~ r2_hidden(D_547,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4881,c_7382])).

tff(c_7597,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ r2_hidden('#skF_16','#skF_14') ),
    inference(resolution,[status(thm)],[c_4004,c_7590])).

tff(c_7605,plain,(
    r2_hidden('#skF_16','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6334,c_7597])).

tff(c_7615,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_7605,c_10])).

tff(c_7621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_7615])).

tff(c_7622,plain,(
    r2_hidden('#skF_16','#skF_14') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_7623,plain,(
    r1_xboole_0('#skF_17','#skF_18') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_160,plain,
    ( r2_hidden('#skF_16','#skF_15')
    | ~ r1_xboole_0('#skF_17','#skF_18') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7724,plain,(
    r2_hidden('#skF_16','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7623,c_160])).

tff(c_158,plain,
    ( r1_xboole_0('#skF_14','#skF_15')
    | ~ r1_xboole_0('#skF_17','#skF_18') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7649,plain,(
    r1_xboole_0('#skF_14','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7623,c_158])).

tff(c_7775,plain,(
    ! [A_563,B_564] :
      ( k3_xboole_0(A_563,B_564) = '#skF_8'
      | ~ r1_xboole_0(A_563,B_564) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_72])).

tff(c_7789,plain,(
    k3_xboole_0('#skF_14','#skF_15') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7649,c_7775])).

tff(c_8385,plain,(
    ! [D_631,A_632,B_633] :
      ( r2_hidden(D_631,k3_xboole_0(A_632,B_633))
      | ~ r2_hidden(D_631,B_633)
      | ~ r2_hidden(D_631,A_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8480,plain,(
    ! [D_638] :
      ( r2_hidden(D_638,'#skF_8')
      | ~ r2_hidden(D_638,'#skF_15')
      | ~ r2_hidden(D_638,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7789,c_8385])).

tff(c_8486,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ r2_hidden('#skF_16','#skF_14') ),
    inference(resolution,[status(thm)],[c_7724,c_8480])).

tff(c_8494,plain,(
    r2_hidden('#skF_16','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7622,c_8486])).

tff(c_8502,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_8494,c_10])).

tff(c_8507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_8502])).
%------------------------------------------------------------------------------
