%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 48.76s
% Output     : CNFRefutation 48.76s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 377 expanded)
%              Number of leaves         :   42 ( 142 expanded)
%              Depth                    :   14
%              Number of atoms          :  219 ( 725 expanded)
%              Number of equality atoms :   53 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_7 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_51,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_122,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_148,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_3'(A_82,B_83),A_82)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_82,B_83] :
      ( ~ v1_xboole_0(A_82)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_3287,plain,(
    ! [A_255,B_256] :
      ( r2_hidden(k4_tarski('#skF_6'(A_255,B_256),'#skF_5'(A_255,B_256)),A_255)
      | r2_hidden('#skF_7'(A_255,B_256),B_256)
      | k2_relat_1(A_255) = B_256 ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5813,plain,(
    ! [A_345,B_346] :
      ( ~ v1_xboole_0(A_345)
      | r2_hidden('#skF_7'(A_345,B_346),B_346)
      | k2_relat_1(A_345) = B_346 ) ),
    inference(resolution,[status(thm)],[c_3287,c_2])).

tff(c_169,plain,(
    ! [A_84,B_85] :
      ( ~ v1_xboole_0(A_84)
      | r1_xboole_0(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = A_86
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_169,c_28])).

tff(c_181,plain,(
    ! [B_87] : k4_xboole_0('#skF_2',B_87) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_199,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,(
    ! [B_95] : k3_xboole_0('#skF_2',B_95) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_199])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [B_95,C_14] :
      ( ~ r1_xboole_0('#skF_2',B_95)
      | ~ r2_hidden(C_14,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_16])).

tff(c_383,plain,(
    ! [C_14] : ~ r2_hidden(C_14,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_6321,plain,(
    ! [A_349] :
      ( ~ v1_xboole_0(A_349)
      | k2_relat_1(A_349) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_5813,c_383])).

tff(c_6365,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_6321])).

tff(c_255,plain,(
    ! [B_94] : k3_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_24])).

tff(c_260,plain,(
    ! [B_94,C_14] :
      ( ~ r1_xboole_0(k1_xboole_0,B_94)
      | ~ r2_hidden(C_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_16])).

tff(c_334,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_5960,plain,(
    ! [A_347] :
      ( ~ v1_xboole_0(A_347)
      | k2_relat_1(A_347) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5813,c_334])).

tff(c_6040,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_5960])).

tff(c_6366,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6365,c_6040])).

tff(c_74,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10')
    | k10_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_127,plain,(
    k10_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_6477,plain,(
    k10_relat_1('#skF_11','#skF_10') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6366,c_127])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_62,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_9'(A_54,B_55,C_56),B_55)
      | ~ r2_hidden(A_54,k10_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2563,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden('#skF_9'(A_227,B_228,C_229),k2_relat_1(C_229))
      | ~ r2_hidden(A_227,k10_relat_1(C_229,B_228))
      | ~ v1_relat_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_80,plain,
    ( k10_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_164,plain,(
    r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_80])).

tff(c_792,plain,(
    ! [A_134,B_135,C_136] :
      ( ~ r1_xboole_0(A_134,B_135)
      | ~ r2_hidden(C_136,B_135)
      | ~ r2_hidden(C_136,A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_824,plain,(
    ! [C_136] :
      ( ~ r2_hidden(C_136,'#skF_10')
      | ~ r2_hidden(C_136,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_164,c_792])).

tff(c_2588,plain,(
    ! [A_227,B_228] :
      ( ~ r2_hidden('#skF_9'(A_227,B_228,'#skF_11'),'#skF_10')
      | ~ r2_hidden(A_227,k10_relat_1('#skF_11',B_228))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_2563,c_824])).

tff(c_2704,plain,(
    ! [A_232,B_233] :
      ( ~ r2_hidden('#skF_9'(A_232,B_233,'#skF_11'),'#skF_10')
      | ~ r2_hidden(A_232,k10_relat_1('#skF_11',B_233)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2588])).

tff(c_2708,plain,(
    ! [A_54] :
      ( ~ r2_hidden(A_54,k10_relat_1('#skF_11','#skF_10'))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_62,c_2704])).

tff(c_2718,plain,(
    ! [A_234] : ~ r2_hidden(A_234,k10_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2708])).

tff(c_2753,plain,(
    v1_xboole_0(k10_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_2718])).

tff(c_6360,plain,(
    k2_relat_1(k10_relat_1('#skF_11','#skF_10')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2753,c_6321])).

tff(c_2714,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k10_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2708])).

tff(c_6921,plain,(
    ! [A_362] :
      ( ~ v1_xboole_0(A_362)
      | k2_relat_1(A_362) = k10_relat_1('#skF_11','#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5813,c_2714])).

tff(c_6933,plain,(
    k2_relat_1(k10_relat_1('#skF_11','#skF_10')) = k10_relat_1('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_2753,c_6921])).

tff(c_6950,plain,(
    k10_relat_1('#skF_11','#skF_10') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6360,c_6933])).

tff(c_6952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6477,c_6950])).

tff(c_6954,plain,(
    ! [B_363] : ~ r1_xboole_0('#skF_2',B_363) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_6958,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_6954])).

tff(c_6966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6958])).

tff(c_6968,plain,(
    ! [B_364] : ~ r1_xboole_0(k1_xboole_0,B_364) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_6976,plain,(
    ! [B_24] : k4_xboole_0(k1_xboole_0,B_24) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_6968])).

tff(c_6981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6976])).

tff(c_6982,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7069,plain,(
    ! [A_386,B_387] :
      ( r2_hidden('#skF_3'(A_386,B_387),B_387)
      | r1_xboole_0(A_386,B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7076,plain,(
    ! [A_386,B_387] :
      ( m1_subset_1('#skF_3'(A_386,B_387),B_387)
      | r1_xboole_0(A_386,B_387) ) ),
    inference(resolution,[status(thm)],[c_7069,c_46])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_3'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7078,plain,(
    ! [B_388,A_389] :
      ( ~ v1_xboole_0(B_388)
      | r1_xboole_0(A_389,B_388) ) ),
    inference(resolution,[status(thm)],[c_7069,c_2])).

tff(c_7086,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_7078,c_6982])).

tff(c_7021,plain,(
    ! [A_377,B_378] :
      ( r2_hidden('#skF_3'(A_377,B_378),A_377)
      | r1_xboole_0(A_377,B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7030,plain,(
    ! [A_379,B_380] :
      ( ~ v1_xboole_0(A_379)
      | r1_xboole_0(A_379,B_380) ) ),
    inference(resolution,[status(thm)],[c_7021,c_2])).

tff(c_7048,plain,(
    ! [A_383,B_384] :
      ( k4_xboole_0(A_383,B_384) = A_383
      | ~ v1_xboole_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_7030,c_28])).

tff(c_7051,plain,(
    ! [B_384] : k4_xboole_0('#skF_2',B_384) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_7048])).

tff(c_7150,plain,(
    ! [A_398,B_399] : k4_xboole_0(A_398,k4_xboole_0(A_398,B_399)) = k3_xboole_0(A_398,B_399) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7176,plain,(
    ! [B_384] : k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2',B_384) ),
    inference(superposition,[status(thm),theory(equality)],[c_7051,c_7150])).

tff(c_7193,plain,(
    ! [B_384] : k3_xboole_0('#skF_2',B_384) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7051,c_7176])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_3'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7195,plain,(
    ! [B_400] : k3_xboole_0(k1_xboole_0,B_400) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7150,c_24])).

tff(c_7200,plain,(
    ! [B_400,C_14] :
      ( ~ r1_xboole_0(k1_xboole_0,B_400)
      | ~ r2_hidden(C_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7195,c_16])).

tff(c_7292,plain,(
    ! [C_409] : ~ r2_hidden(C_409,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7200])).

tff(c_7310,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_7292])).

tff(c_7096,plain,(
    ! [A_392,B_393] :
      ( k4_xboole_0(A_392,B_393) = A_392
      | ~ v1_xboole_0(B_393) ) ),
    inference(resolution,[status(thm)],[c_7078,c_28])).

tff(c_7099,plain,(
    ! [A_392] : k4_xboole_0(A_392,'#skF_2') = A_392 ),
    inference(resolution,[status(thm)],[c_6,c_7096])).

tff(c_7173,plain,(
    ! [A_392] : k4_xboole_0(A_392,A_392) = k3_xboole_0(A_392,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7099,c_7150])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7183,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7150])).

tff(c_7406,plain,(
    ! [A_416] : k3_xboole_0(A_416,k1_xboole_0) = k3_xboole_0(A_416,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7173,c_7183])).

tff(c_7420,plain,(
    ! [A_416,C_14] :
      ( ~ r1_xboole_0(A_416,k1_xboole_0)
      | ~ r2_hidden(C_14,k3_xboole_0(A_416,'#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7406,c_16])).

tff(c_7440,plain,(
    ! [C_417,A_418] : ~ r2_hidden(C_417,k3_xboole_0(A_418,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7310,c_7420])).

tff(c_7443,plain,(
    ! [C_417] : ~ r2_hidden(C_417,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7193,c_7440])).

tff(c_8352,plain,(
    ! [A_488,B_489] :
      ( r2_hidden(k4_tarski('#skF_6'(A_488,B_489),'#skF_5'(A_488,B_489)),A_488)
      | r2_hidden('#skF_7'(A_488,B_489),B_489)
      | k2_relat_1(A_488) = B_489 ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10935,plain,(
    ! [A_574,B_575] :
      ( ~ v1_xboole_0(A_574)
      | r2_hidden('#skF_7'(A_574,B_575),B_575)
      | k2_relat_1(A_574) = B_575 ) ),
    inference(resolution,[status(thm)],[c_8352,c_2])).

tff(c_11288,plain,(
    ! [B_577,A_578] :
      ( ~ v1_xboole_0(B_577)
      | ~ v1_xboole_0(A_578)
      | k2_relat_1(A_578) = B_577 ) ),
    inference(resolution,[status(thm)],[c_10935,c_2])).

tff(c_11318,plain,(
    ! [A_579] :
      ( ~ v1_xboole_0(A_579)
      | k2_relat_1(A_579) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_6,c_11288])).

tff(c_11354,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_11318])).

tff(c_7281,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7200])).

tff(c_11043,plain,(
    ! [A_576] :
      ( ~ v1_xboole_0(A_576)
      | k2_relat_1(A_576) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10935,c_7281])).

tff(c_11103,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_11043])).

tff(c_11355,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11354,c_11103])).

tff(c_6983,plain,(
    k10_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_11438,plain,(
    k10_relat_1('#skF_11','#skF_10') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11355,c_6983])).

tff(c_48,plain,(
    ! [A_35,C_50] :
      ( r2_hidden(k4_tarski('#skF_8'(A_35,k2_relat_1(A_35),C_50),C_50),A_35)
      | ~ r2_hidden(C_50,k2_relat_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( r2_hidden(B_32,A_31)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8580,plain,(
    ! [A_501,C_502,B_503,D_504] :
      ( r2_hidden(A_501,k10_relat_1(C_502,B_503))
      | ~ r2_hidden(D_504,B_503)
      | ~ r2_hidden(k4_tarski(A_501,D_504),C_502)
      | ~ r2_hidden(D_504,k2_relat_1(C_502))
      | ~ v1_relat_1(C_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18592,plain,(
    ! [A_781,C_782,A_783,B_784] :
      ( r2_hidden(A_781,k10_relat_1(C_782,A_783))
      | ~ r2_hidden(k4_tarski(A_781,B_784),C_782)
      | ~ r2_hidden(B_784,k2_relat_1(C_782))
      | ~ v1_relat_1(C_782)
      | ~ m1_subset_1(B_784,A_783)
      | v1_xboole_0(A_783) ) ),
    inference(resolution,[status(thm)],[c_40,c_8580])).

tff(c_222119,plain,(
    ! [A_26757,C_26758,A_26759] :
      ( r2_hidden('#skF_8'(A_26757,k2_relat_1(A_26757),C_26758),k10_relat_1(A_26757,A_26759))
      | ~ v1_relat_1(A_26757)
      | ~ m1_subset_1(C_26758,A_26759)
      | v1_xboole_0(A_26759)
      | ~ r2_hidden(C_26758,k2_relat_1(A_26757)) ) ),
    inference(resolution,[status(thm)],[c_48,c_18592])).

tff(c_222611,plain,(
    ! [C_26758] :
      ( r2_hidden('#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_26758),'#skF_2')
      | ~ v1_relat_1('#skF_11')
      | ~ m1_subset_1(C_26758,'#skF_10')
      | v1_xboole_0('#skF_10')
      | ~ r2_hidden(C_26758,k2_relat_1('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11438,c_222119])).

tff(c_222773,plain,(
    ! [C_26758] :
      ( r2_hidden('#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_26758),'#skF_2')
      | ~ m1_subset_1(C_26758,'#skF_10')
      | v1_xboole_0('#skF_10')
      | ~ r2_hidden(C_26758,k2_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_222611])).

tff(c_222775,plain,(
    ! [C_26791] :
      ( ~ m1_subset_1(C_26791,'#skF_10')
      | ~ r2_hidden(C_26791,k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7086,c_7443,c_222773])).

tff(c_223699,plain,(
    ! [B_26949] :
      ( ~ m1_subset_1('#skF_3'(k2_relat_1('#skF_11'),B_26949),'#skF_10')
      | r1_xboole_0(k2_relat_1('#skF_11'),B_26949) ) ),
    inference(resolution,[status(thm)],[c_12,c_222775])).

tff(c_223735,plain,(
    r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_7076,c_223699])).

tff(c_223742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6982,c_6982,c_223735])).

tff(c_223744,plain,(
    ! [B_26981] : ~ r1_xboole_0(k1_xboole_0,B_26981) ),
    inference(splitRight,[status(thm)],[c_7200])).

tff(c_223755,plain,(
    ! [B_24] : k4_xboole_0(k1_xboole_0,B_24) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_223744])).

tff(c_223761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_223755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.76/37.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.76/37.62  
% 48.76/37.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.76/37.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_7 > #skF_5 > #skF_4
% 48.76/37.62  
% 48.76/37.62  %Foreground sorts:
% 48.76/37.62  
% 48.76/37.62  
% 48.76/37.62  %Background operators:
% 48.76/37.62  
% 48.76/37.62  
% 48.76/37.62  %Foreground operators:
% 48.76/37.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 48.76/37.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.76/37.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.76/37.62  tff('#skF_11', type, '#skF_11': $i).
% 48.76/37.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 48.76/37.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 48.76/37.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 48.76/37.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 48.76/37.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.76/37.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 48.76/37.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.76/37.62  tff('#skF_10', type, '#skF_10': $i).
% 48.76/37.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.76/37.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 48.76/37.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 48.76/37.62  tff('#skF_2', type, '#skF_2': $i).
% 48.76/37.62  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 48.76/37.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.76/37.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 48.76/37.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.76/37.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.76/37.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 48.76/37.62  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 48.76/37.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 48.76/37.62  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 48.76/37.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 48.76/37.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 48.76/37.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 48.76/37.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.76/37.62  
% 48.76/37.64  tff(f_73, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 48.76/37.64  tff(f_83, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 48.76/37.64  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 48.76/37.64  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 48.76/37.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 48.76/37.64  tff(f_122, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 48.76/37.64  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 48.76/37.64  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 48.76/37.64  tff(f_148, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 48.76/37.64  tff(f_133, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 48.76/37.64  tff(f_114, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 48.76/37.64  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 48.76/37.64  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 48.76/37.64  tff(c_24, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 48.76/37.64  tff(c_30, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 48.76/37.64  tff(c_6, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_33])).
% 48.76/37.64  tff(c_155, plain, (![A_82, B_83]: (r2_hidden('#skF_3'(A_82, B_83), A_82) | r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 48.76/37.64  tff(c_163, plain, (![A_82, B_83]: (~v1_xboole_0(A_82) | r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_155, c_2])).
% 48.76/37.64  tff(c_3287, plain, (![A_255, B_256]: (r2_hidden(k4_tarski('#skF_6'(A_255, B_256), '#skF_5'(A_255, B_256)), A_255) | r2_hidden('#skF_7'(A_255, B_256), B_256) | k2_relat_1(A_255)=B_256)), inference(cnfTransformation, [status(thm)], [f_122])).
% 48.76/37.64  tff(c_5813, plain, (![A_345, B_346]: (~v1_xboole_0(A_345) | r2_hidden('#skF_7'(A_345, B_346), B_346) | k2_relat_1(A_345)=B_346)), inference(resolution, [status(thm)], [c_3287, c_2])).
% 48.76/37.64  tff(c_169, plain, (![A_84, B_85]: (~v1_xboole_0(A_84) | r1_xboole_0(A_84, B_85))), inference(resolution, [status(thm)], [c_155, c_2])).
% 48.76/37.64  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 48.76/37.64  tff(c_178, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=A_86 | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_169, c_28])).
% 48.76/37.64  tff(c_181, plain, (![B_87]: (k4_xboole_0('#skF_2', B_87)='#skF_2')), inference(resolution, [status(thm)], [c_6, c_178])).
% 48.76/37.64  tff(c_199, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 48.76/37.64  tff(c_274, plain, (![B_95]: (k3_xboole_0('#skF_2', B_95)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_181, c_199])).
% 48.76/37.64  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 48.76/37.64  tff(c_279, plain, (![B_95, C_14]: (~r1_xboole_0('#skF_2', B_95) | ~r2_hidden(C_14, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_16])).
% 48.76/37.64  tff(c_383, plain, (![C_14]: (~r2_hidden(C_14, '#skF_2'))), inference(splitLeft, [status(thm)], [c_279])).
% 48.76/37.64  tff(c_6321, plain, (![A_349]: (~v1_xboole_0(A_349) | k2_relat_1(A_349)='#skF_2')), inference(resolution, [status(thm)], [c_5813, c_383])).
% 48.76/37.64  tff(c_6365, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_6321])).
% 48.76/37.64  tff(c_255, plain, (![B_94]: (k3_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_24])).
% 48.76/37.64  tff(c_260, plain, (![B_94, C_14]: (~r1_xboole_0(k1_xboole_0, B_94) | ~r2_hidden(C_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_255, c_16])).
% 48.76/37.64  tff(c_334, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_260])).
% 48.76/37.64  tff(c_5960, plain, (![A_347]: (~v1_xboole_0(A_347) | k2_relat_1(A_347)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5813, c_334])).
% 48.76/37.64  tff(c_6040, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_5960])).
% 48.76/37.64  tff(c_6366, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6365, c_6040])).
% 48.76/37.64  tff(c_74, plain, (~r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10') | k10_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_148])).
% 48.76/37.64  tff(c_127, plain, (k10_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 48.76/37.64  tff(c_6477, plain, (k10_relat_1('#skF_11', '#skF_10')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6366, c_127])).
% 48.76/37.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 48.76/37.64  tff(c_72, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_148])).
% 48.76/37.64  tff(c_62, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_9'(A_54, B_55, C_56), B_55) | ~r2_hidden(A_54, k10_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_133])).
% 48.76/37.64  tff(c_2563, plain, (![A_227, B_228, C_229]: (r2_hidden('#skF_9'(A_227, B_228, C_229), k2_relat_1(C_229)) | ~r2_hidden(A_227, k10_relat_1(C_229, B_228)) | ~v1_relat_1(C_229))), inference(cnfTransformation, [status(thm)], [f_133])).
% 48.76/37.64  tff(c_80, plain, (k10_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_148])).
% 48.76/37.64  tff(c_164, plain, (r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_127, c_80])).
% 48.76/37.64  tff(c_792, plain, (![A_134, B_135, C_136]: (~r1_xboole_0(A_134, B_135) | ~r2_hidden(C_136, B_135) | ~r2_hidden(C_136, A_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_824, plain, (![C_136]: (~r2_hidden(C_136, '#skF_10') | ~r2_hidden(C_136, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_164, c_792])).
% 48.76/37.64  tff(c_2588, plain, (![A_227, B_228]: (~r2_hidden('#skF_9'(A_227, B_228, '#skF_11'), '#skF_10') | ~r2_hidden(A_227, k10_relat_1('#skF_11', B_228)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_2563, c_824])).
% 48.76/37.64  tff(c_2704, plain, (![A_232, B_233]: (~r2_hidden('#skF_9'(A_232, B_233, '#skF_11'), '#skF_10') | ~r2_hidden(A_232, k10_relat_1('#skF_11', B_233)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2588])).
% 48.76/37.64  tff(c_2708, plain, (![A_54]: (~r2_hidden(A_54, k10_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_62, c_2704])).
% 48.76/37.64  tff(c_2718, plain, (![A_234]: (~r2_hidden(A_234, k10_relat_1('#skF_11', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2708])).
% 48.76/37.64  tff(c_2753, plain, (v1_xboole_0(k10_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_4, c_2718])).
% 48.76/37.64  tff(c_6360, plain, (k2_relat_1(k10_relat_1('#skF_11', '#skF_10'))='#skF_2'), inference(resolution, [status(thm)], [c_2753, c_6321])).
% 48.76/37.64  tff(c_2714, plain, (![A_54]: (~r2_hidden(A_54, k10_relat_1('#skF_11', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2708])).
% 48.76/37.64  tff(c_6921, plain, (![A_362]: (~v1_xboole_0(A_362) | k2_relat_1(A_362)=k10_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_5813, c_2714])).
% 48.76/37.64  tff(c_6933, plain, (k2_relat_1(k10_relat_1('#skF_11', '#skF_10'))=k10_relat_1('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_2753, c_6921])).
% 48.76/37.64  tff(c_6950, plain, (k10_relat_1('#skF_11', '#skF_10')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6360, c_6933])).
% 48.76/37.64  tff(c_6952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6477, c_6950])).
% 48.76/37.64  tff(c_6954, plain, (![B_363]: (~r1_xboole_0('#skF_2', B_363))), inference(splitRight, [status(thm)], [c_279])).
% 48.76/37.64  tff(c_6958, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_163, c_6954])).
% 48.76/37.64  tff(c_6966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6958])).
% 48.76/37.64  tff(c_6968, plain, (![B_364]: (~r1_xboole_0(k1_xboole_0, B_364))), inference(splitRight, [status(thm)], [c_260])).
% 48.76/37.64  tff(c_6976, plain, (![B_24]: (k4_xboole_0(k1_xboole_0, B_24)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_6968])).
% 48.76/37.64  tff(c_6981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_6976])).
% 48.76/37.64  tff(c_6982, plain, (~r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_74])).
% 48.76/37.64  tff(c_7069, plain, (![A_386, B_387]: (r2_hidden('#skF_3'(A_386, B_387), B_387) | r1_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_46, plain, (![A_33, B_34]: (m1_subset_1(A_33, B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_114])).
% 48.76/37.64  tff(c_7076, plain, (![A_386, B_387]: (m1_subset_1('#skF_3'(A_386, B_387), B_387) | r1_xboole_0(A_386, B_387))), inference(resolution, [status(thm)], [c_7069, c_46])).
% 48.76/37.64  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_3'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_7078, plain, (![B_388, A_389]: (~v1_xboole_0(B_388) | r1_xboole_0(A_389, B_388))), inference(resolution, [status(thm)], [c_7069, c_2])).
% 48.76/37.64  tff(c_7086, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_7078, c_6982])).
% 48.76/37.64  tff(c_7021, plain, (![A_377, B_378]: (r2_hidden('#skF_3'(A_377, B_378), A_377) | r1_xboole_0(A_377, B_378))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_7030, plain, (![A_379, B_380]: (~v1_xboole_0(A_379) | r1_xboole_0(A_379, B_380))), inference(resolution, [status(thm)], [c_7021, c_2])).
% 48.76/37.64  tff(c_7048, plain, (![A_383, B_384]: (k4_xboole_0(A_383, B_384)=A_383 | ~v1_xboole_0(A_383))), inference(resolution, [status(thm)], [c_7030, c_28])).
% 48.76/37.64  tff(c_7051, plain, (![B_384]: (k4_xboole_0('#skF_2', B_384)='#skF_2')), inference(resolution, [status(thm)], [c_6, c_7048])).
% 48.76/37.64  tff(c_7150, plain, (![A_398, B_399]: (k4_xboole_0(A_398, k4_xboole_0(A_398, B_399))=k3_xboole_0(A_398, B_399))), inference(cnfTransformation, [status(thm)], [f_71])).
% 48.76/37.64  tff(c_7176, plain, (![B_384]: (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', B_384))), inference(superposition, [status(thm), theory('equality')], [c_7051, c_7150])).
% 48.76/37.64  tff(c_7193, plain, (![B_384]: (k3_xboole_0('#skF_2', B_384)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7051, c_7176])).
% 48.76/37.64  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_3'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.76/37.64  tff(c_7195, plain, (![B_400]: (k3_xboole_0(k1_xboole_0, B_400)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7150, c_24])).
% 48.76/37.64  tff(c_7200, plain, (![B_400, C_14]: (~r1_xboole_0(k1_xboole_0, B_400) | ~r2_hidden(C_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7195, c_16])).
% 48.76/37.64  tff(c_7292, plain, (![C_409]: (~r2_hidden(C_409, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_7200])).
% 48.76/37.64  tff(c_7310, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_7292])).
% 48.76/37.64  tff(c_7096, plain, (![A_392, B_393]: (k4_xboole_0(A_392, B_393)=A_392 | ~v1_xboole_0(B_393))), inference(resolution, [status(thm)], [c_7078, c_28])).
% 48.76/37.64  tff(c_7099, plain, (![A_392]: (k4_xboole_0(A_392, '#skF_2')=A_392)), inference(resolution, [status(thm)], [c_6, c_7096])).
% 48.76/37.64  tff(c_7173, plain, (![A_392]: (k4_xboole_0(A_392, A_392)=k3_xboole_0(A_392, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7099, c_7150])).
% 48.76/37.64  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 48.76/37.64  tff(c_7183, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7150])).
% 48.76/37.64  tff(c_7406, plain, (![A_416]: (k3_xboole_0(A_416, k1_xboole_0)=k3_xboole_0(A_416, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7173, c_7183])).
% 48.76/37.64  tff(c_7420, plain, (![A_416, C_14]: (~r1_xboole_0(A_416, k1_xboole_0) | ~r2_hidden(C_14, k3_xboole_0(A_416, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7406, c_16])).
% 48.76/37.64  tff(c_7440, plain, (![C_417, A_418]: (~r2_hidden(C_417, k3_xboole_0(A_418, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7310, c_7420])).
% 48.76/37.64  tff(c_7443, plain, (![C_417]: (~r2_hidden(C_417, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7193, c_7440])).
% 48.76/37.64  tff(c_8352, plain, (![A_488, B_489]: (r2_hidden(k4_tarski('#skF_6'(A_488, B_489), '#skF_5'(A_488, B_489)), A_488) | r2_hidden('#skF_7'(A_488, B_489), B_489) | k2_relat_1(A_488)=B_489)), inference(cnfTransformation, [status(thm)], [f_122])).
% 48.76/37.64  tff(c_10935, plain, (![A_574, B_575]: (~v1_xboole_0(A_574) | r2_hidden('#skF_7'(A_574, B_575), B_575) | k2_relat_1(A_574)=B_575)), inference(resolution, [status(thm)], [c_8352, c_2])).
% 48.76/37.64  tff(c_11288, plain, (![B_577, A_578]: (~v1_xboole_0(B_577) | ~v1_xboole_0(A_578) | k2_relat_1(A_578)=B_577)), inference(resolution, [status(thm)], [c_10935, c_2])).
% 48.76/37.64  tff(c_11318, plain, (![A_579]: (~v1_xboole_0(A_579) | k2_relat_1(A_579)='#skF_2')), inference(resolution, [status(thm)], [c_6, c_11288])).
% 48.76/37.64  tff(c_11354, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_11318])).
% 48.76/37.64  tff(c_7281, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_7200])).
% 48.76/37.64  tff(c_11043, plain, (![A_576]: (~v1_xboole_0(A_576) | k2_relat_1(A_576)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10935, c_7281])).
% 48.76/37.64  tff(c_11103, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_11043])).
% 48.76/37.64  tff(c_11355, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11354, c_11103])).
% 48.76/37.64  tff(c_6983, plain, (k10_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 48.76/37.64  tff(c_11438, plain, (k10_relat_1('#skF_11', '#skF_10')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11355, c_6983])).
% 48.76/37.64  tff(c_48, plain, (![A_35, C_50]: (r2_hidden(k4_tarski('#skF_8'(A_35, k2_relat_1(A_35), C_50), C_50), A_35) | ~r2_hidden(C_50, k2_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 48.76/37.64  tff(c_40, plain, (![B_32, A_31]: (r2_hidden(B_32, A_31) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 48.76/37.64  tff(c_8580, plain, (![A_501, C_502, B_503, D_504]: (r2_hidden(A_501, k10_relat_1(C_502, B_503)) | ~r2_hidden(D_504, B_503) | ~r2_hidden(k4_tarski(A_501, D_504), C_502) | ~r2_hidden(D_504, k2_relat_1(C_502)) | ~v1_relat_1(C_502))), inference(cnfTransformation, [status(thm)], [f_133])).
% 48.76/37.64  tff(c_18592, plain, (![A_781, C_782, A_783, B_784]: (r2_hidden(A_781, k10_relat_1(C_782, A_783)) | ~r2_hidden(k4_tarski(A_781, B_784), C_782) | ~r2_hidden(B_784, k2_relat_1(C_782)) | ~v1_relat_1(C_782) | ~m1_subset_1(B_784, A_783) | v1_xboole_0(A_783))), inference(resolution, [status(thm)], [c_40, c_8580])).
% 48.76/37.64  tff(c_222119, plain, (![A_26757, C_26758, A_26759]: (r2_hidden('#skF_8'(A_26757, k2_relat_1(A_26757), C_26758), k10_relat_1(A_26757, A_26759)) | ~v1_relat_1(A_26757) | ~m1_subset_1(C_26758, A_26759) | v1_xboole_0(A_26759) | ~r2_hidden(C_26758, k2_relat_1(A_26757)))), inference(resolution, [status(thm)], [c_48, c_18592])).
% 48.76/37.64  tff(c_222611, plain, (![C_26758]: (r2_hidden('#skF_8'('#skF_11', k2_relat_1('#skF_11'), C_26758), '#skF_2') | ~v1_relat_1('#skF_11') | ~m1_subset_1(C_26758, '#skF_10') | v1_xboole_0('#skF_10') | ~r2_hidden(C_26758, k2_relat_1('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_11438, c_222119])).
% 48.76/37.64  tff(c_222773, plain, (![C_26758]: (r2_hidden('#skF_8'('#skF_11', k2_relat_1('#skF_11'), C_26758), '#skF_2') | ~m1_subset_1(C_26758, '#skF_10') | v1_xboole_0('#skF_10') | ~r2_hidden(C_26758, k2_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_222611])).
% 48.76/37.64  tff(c_222775, plain, (![C_26791]: (~m1_subset_1(C_26791, '#skF_10') | ~r2_hidden(C_26791, k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_7086, c_7443, c_222773])).
% 48.76/37.64  tff(c_223699, plain, (![B_26949]: (~m1_subset_1('#skF_3'(k2_relat_1('#skF_11'), B_26949), '#skF_10') | r1_xboole_0(k2_relat_1('#skF_11'), B_26949))), inference(resolution, [status(thm)], [c_12, c_222775])).
% 48.76/37.64  tff(c_223735, plain, (r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_7076, c_223699])).
% 48.76/37.64  tff(c_223742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6982, c_6982, c_223735])).
% 48.76/37.64  tff(c_223744, plain, (![B_26981]: (~r1_xboole_0(k1_xboole_0, B_26981))), inference(splitRight, [status(thm)], [c_7200])).
% 48.76/37.64  tff(c_223755, plain, (![B_24]: (k4_xboole_0(k1_xboole_0, B_24)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_223744])).
% 48.76/37.64  tff(c_223761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_223755])).
% 48.76/37.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.76/37.64  
% 48.76/37.64  Inference rules
% 48.76/37.64  ----------------------
% 48.76/37.64  #Ref     : 11
% 48.76/37.64  #Sup     : 53204
% 48.76/37.64  #Fact    : 0
% 48.76/37.64  #Define  : 0
% 48.76/37.64  #Split   : 38
% 48.76/37.64  #Chain   : 0
% 48.76/37.64  #Close   : 0
% 48.76/37.64  
% 48.76/37.64  Ordering : KBO
% 48.76/37.64  
% 48.76/37.64  Simplification rules
% 48.76/37.64  ----------------------
% 48.76/37.64  #Subsume      : 18963
% 48.76/37.64  #Demod        : 27729
% 48.76/37.64  #Tautology    : 15211
% 48.76/37.64  #SimpNegUnit  : 1968
% 48.76/37.64  #BackRed      : 825
% 48.76/37.64  
% 48.76/37.64  #Partial instantiations: 16000
% 48.76/37.64  #Strategies tried      : 1
% 48.76/37.64  
% 48.76/37.64  Timing (in seconds)
% 48.76/37.64  ----------------------
% 48.76/37.66  Preprocessing        : 0.42
% 48.76/37.66  Parsing              : 0.18
% 48.76/37.66  CNF conversion       : 0.05
% 48.76/37.66  Main loop            : 36.43
% 48.76/37.66  Inferencing          : 3.67
% 48.76/37.66  Reduction            : 9.32
% 48.76/37.66  Demodulation         : 6.76
% 48.76/37.66  BG Simplification    : 0.45
% 48.76/37.66  Subsumption          : 20.85
% 48.76/37.66  Abstraction          : 0.67
% 48.76/37.66  MUC search           : 0.00
% 48.76/37.66  Cooper               : 0.00
% 48.76/37.66  Total                : 36.90
% 48.76/37.66  Index Insertion      : 0.00
% 48.76/37.66  Index Deletion       : 0.00
% 48.76/37.66  Index Matching       : 0.00
% 48.76/37.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
