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
% DateTime   : Thu Dec  3 10:06:24 EST 2020

% Result     : Theorem 20.18s
% Output     : CNFRefutation 20.35s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 360 expanded)
%              Number of leaves         :   49 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 ( 755 expanded)
%              Number of equality atoms :   53 ( 118 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_101,axiom,(
    ! [A] :
      ( v4_ordinal1(A)
    <=> A = k3_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( v4_ordinal1(A)
        <=> ! [B] :
              ( v3_ordinal1(B)
             => ( r2_hidden(B,A)
               => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_138,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_143,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_127,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_88,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_90,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_73,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_131,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_106,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_42,plain,(
    ! [C_34,A_19] :
      ( r2_hidden(C_34,'#skF_6'(A_19,k3_tarski(A_19),C_34))
      | ~ r2_hidden(C_34,k3_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12132,plain,(
    ! [A_544,C_545] :
      ( r2_hidden('#skF_6'(A_544,k3_tarski(A_544),C_545),A_544)
      | ~ r2_hidden(C_545,k3_tarski(A_544)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_38781,plain,(
    ! [A_1207,C_1208] :
      ( ~ r2_hidden(A_1207,'#skF_6'(A_1207,k3_tarski(A_1207),C_1208))
      | ~ r2_hidden(C_1208,k3_tarski(A_1207)) ) ),
    inference(resolution,[status(thm)],[c_12132,c_2])).

tff(c_38841,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k3_tarski(A_19)) ),
    inference(resolution,[status(thm)],[c_42,c_38781])).

tff(c_140,plain,(
    ! [A_75] :
      ( v4_ordinal1(A_75)
      | k3_tarski(A_75) != A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_104,plain,
    ( v3_ordinal1('#skF_11')
    | ~ v4_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_120,plain,(
    ~ v4_ordinal1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_144,plain,(
    k3_tarski('#skF_10') != '#skF_10' ),
    inference(resolution,[status(thm)],[c_140,c_120])).

tff(c_98,plain,(
    v3_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_92,plain,(
    ! [A_61] :
      ( ~ v3_ordinal1('#skF_9'(A_61))
      | v3_ordinal1(k3_tarski(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_114,plain,(
    ! [B_67] :
      ( v4_ordinal1('#skF_10')
      | r2_hidden(k1_ordinal1(B_67),'#skF_10')
      | ~ r2_hidden(B_67,'#skF_10')
      | ~ v3_ordinal1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_243,plain,(
    ! [B_67] :
      ( r2_hidden(k1_ordinal1(B_67),'#skF_10')
      | ~ r2_hidden(B_67,'#skF_10')
      | ~ v3_ordinal1(B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_114])).

tff(c_443,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(A_110,k3_tarski(B_111))
      | ~ r2_hidden(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_82,plain,(
    ! [A_53] : r2_hidden(A_53,k1_ordinal1(A_53)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_226,plain,(
    ! [B_87,A_88] :
      ( ~ r1_tarski(B_87,A_88)
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_234,plain,(
    ! [A_53] : ~ r1_tarski(k1_ordinal1(A_53),A_53) ),
    inference(resolution,[status(thm)],[c_82,c_226])).

tff(c_464,plain,(
    ! [B_112] : ~ r2_hidden(k1_ordinal1(k3_tarski(B_112)),B_112) ),
    inference(resolution,[status(thm)],[c_443,c_234])).

tff(c_475,plain,
    ( ~ r2_hidden(k3_tarski('#skF_10'),'#skF_10')
    | ~ v3_ordinal1(k3_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_243,c_464])).

tff(c_528,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_532,plain,(
    ~ v3_ordinal1('#skF_9'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_92,c_528])).

tff(c_94,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_9'(A_61),A_61)
      | v3_ordinal1(k3_tarski(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_360,plain,(
    ! [A_106,B_107] :
      ( v3_ordinal1(A_106)
      | ~ r2_hidden(A_106,B_107)
      | ~ v3_ordinal1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4696,plain,(
    ! [A_281] :
      ( v3_ordinal1('#skF_9'(A_281))
      | ~ v3_ordinal1(A_281)
      | v3_ordinal1(k3_tarski(A_281)) ) ),
    inference(resolution,[status(thm)],[c_94,c_360])).

tff(c_4705,plain,
    ( v3_ordinal1('#skF_9'('#skF_10'))
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_4696,c_528])).

tff(c_4737,plain,(
    v3_ordinal1('#skF_9'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_4705])).

tff(c_4739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_4737])).

tff(c_4741,plain,(
    v3_ordinal1(k3_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_17440,plain,(
    ! [B_711,A_712] :
      ( r2_hidden(B_711,A_712)
      | B_711 = A_712
      | r2_hidden(A_712,B_711)
      | ~ v3_ordinal1(B_711)
      | ~ v3_ordinal1(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4740,plain,(
    ~ r2_hidden(k3_tarski('#skF_10'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_17588,plain,
    ( k3_tarski('#skF_10') = '#skF_10'
    | r2_hidden('#skF_10',k3_tarski('#skF_10'))
    | ~ v3_ordinal1(k3_tarski('#skF_10'))
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_17440,c_4740])).

tff(c_17865,plain,
    ( k3_tarski('#skF_10') = '#skF_10'
    | r2_hidden('#skF_10',k3_tarski('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_4741,c_17588])).

tff(c_17866,plain,(
    r2_hidden('#skF_10',k3_tarski('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_17865])).

tff(c_38849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38841,c_17866])).

tff(c_38850,plain,(
    v3_ordinal1('#skF_11') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_38863,plain,(
    ! [A_1210] :
      ( v1_ordinal1(A_1210)
      | ~ v3_ordinal1(A_1210) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38870,plain,(
    v1_ordinal1('#skF_11') ),
    inference(resolution,[status(thm)],[c_38850,c_38863])).

tff(c_38851,plain,(
    v4_ordinal1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_102,plain,
    ( r2_hidden('#skF_11','#skF_10')
    | ~ v4_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38853,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38851,c_102])).

tff(c_70,plain,(
    ! [A_47] : k2_xboole_0(A_47,k1_tarski(A_47)) = k1_ordinal1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    ! [A_40] : k3_tarski(k1_tarski(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_39696,plain,(
    ! [A_1287,B_1288] : k2_xboole_0(k3_tarski(A_1287),k3_tarski(B_1288)) = k3_tarski(k2_xboole_0(A_1287,B_1288)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_71079,plain,(
    ! [A_1901,A_1902] : k3_tarski(k2_xboole_0(A_1901,k1_tarski(A_1902))) = k2_xboole_0(k3_tarski(A_1901),A_1902) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_39696])).

tff(c_71298,plain,(
    ! [A_1903] : k2_xboole_0(k3_tarski(A_1903),A_1903) = k3_tarski(k1_ordinal1(A_1903)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_71079])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71525,plain,(
    ! [A_1903] : k2_xboole_0(A_1903,k3_tarski(A_1903)) = k3_tarski(k1_ordinal1(A_1903)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71298,c_4])).

tff(c_39832,plain,(
    ! [A_1292,B_1293] :
      ( r2_hidden('#skF_7'(A_1292,B_1293),A_1292)
      | r1_tarski(k3_tarski(A_1292),B_1293) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    ! [B_51,A_48] :
      ( r1_tarski(B_51,A_48)
      | ~ r2_hidden(B_51,A_48)
      | ~ v1_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_81616,plain,(
    ! [A_2031,B_2032] :
      ( r1_tarski('#skF_7'(A_2031,B_2032),A_2031)
      | ~ v1_ordinal1(A_2031)
      | r1_tarski(k3_tarski(A_2031),B_2032) ) ),
    inference(resolution,[status(thm)],[c_39832,c_72])).

tff(c_60,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski('#skF_7'(A_41,B_42),B_42)
      | r1_tarski(k3_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_81682,plain,(
    ! [A_2033] :
      ( ~ v1_ordinal1(A_2033)
      | r1_tarski(k3_tarski(A_2033),A_2033) ) ),
    inference(resolution,[status(thm)],[c_81616,c_60])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81694,plain,(
    ! [A_2033] :
      ( k2_xboole_0(k3_tarski(A_2033),A_2033) = A_2033
      | ~ v1_ordinal1(A_2033) ) ),
    inference(resolution,[status(thm)],[c_81682,c_30])).

tff(c_81759,plain,(
    ! [A_2034] :
      ( k3_tarski(k1_ordinal1(A_2034)) = A_2034
      | ~ v1_ordinal1(A_2034) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71525,c_4,c_81694])).

tff(c_90,plain,(
    ! [A_60] :
      ( v3_ordinal1(k1_ordinal1(A_60))
      | ~ v3_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_41200,plain,(
    ! [B_1331,A_1332] :
      ( r2_hidden(B_1331,A_1332)
      | B_1331 = A_1332
      | r2_hidden(A_1332,B_1331)
      | ~ v3_ordinal1(B_1331)
      | ~ v3_ordinal1(A_1332) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_100,plain,
    ( ~ r2_hidden(k1_ordinal1('#skF_11'),'#skF_10')
    | ~ v4_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38900,plain,(
    ~ r2_hidden(k1_ordinal1('#skF_11'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38851,c_100])).

tff(c_41348,plain,
    ( k1_ordinal1('#skF_11') = '#skF_10'
    | r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_11'))
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_41200,c_38900])).

tff(c_41553,plain,
    ( k1_ordinal1('#skF_11') = '#skF_10'
    | r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_41348])).

tff(c_41638,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_41553])).

tff(c_41641,plain,(
    ~ v3_ordinal1('#skF_11') ),
    inference(resolution,[status(thm)],[c_90,c_41638])).

tff(c_41645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38850,c_41641])).

tff(c_41647,plain,(
    v3_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_41553])).

tff(c_68,plain,(
    ! [A_46] :
      ( v1_ordinal1(A_46)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_41660,plain,(
    v1_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_41647,c_68])).

tff(c_41646,plain,
    ( r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | k1_ordinal1('#skF_11') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_41553])).

tff(c_41661,plain,(
    k1_ordinal1('#skF_11') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_41646])).

tff(c_84,plain,(
    ! [A_54] : k1_ordinal1(A_54) != A_54 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_41848,plain,(
    '#skF_11' != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_41661,c_84])).

tff(c_38901,plain,(
    ! [A_1214] :
      ( k3_tarski(A_1214) = A_1214
      | ~ v4_ordinal1(A_1214) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38905,plain,(
    k3_tarski('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_38851,c_38901])).

tff(c_47836,plain,(
    ! [A_1506,B_1507] : k3_tarski(k2_xboole_0(k1_tarski(A_1506),B_1507)) = k2_xboole_0(A_1506,k3_tarski(B_1507)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_39696])).

tff(c_47987,plain,(
    ! [A_1506] : k2_xboole_0(A_1506,k3_tarski(k1_tarski(k1_tarski(A_1506)))) = k3_tarski(k1_ordinal1(k1_tarski(A_1506))) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_47836])).

tff(c_48011,plain,(
    ! [A_1506] : k3_tarski(k1_ordinal1(k1_tarski(A_1506))) = k1_ordinal1(A_1506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_47987])).

tff(c_50332,plain,(
    ! [A_1545,A_1546] : k3_tarski(k2_xboole_0(A_1545,k1_tarski(A_1546))) = k2_xboole_0(k3_tarski(A_1545),A_1546) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_39696])).

tff(c_50564,plain,(
    ! [A_1547] : k2_xboole_0(k3_tarski(A_1547),A_1547) = k3_tarski(k1_ordinal1(A_1547)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_50332])).

tff(c_39752,plain,(
    ! [A_1287,A_40] : k3_tarski(k2_xboole_0(A_1287,k1_tarski(A_40))) = k2_xboole_0(k3_tarski(A_1287),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_39696])).

tff(c_50571,plain,(
    ! [A_40] : k2_xboole_0(k3_tarski(k3_tarski(k1_tarski(A_40))),A_40) = k3_tarski(k3_tarski(k1_ordinal1(k1_tarski(A_40)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_50564,c_39752])).

tff(c_50864,plain,(
    ! [A_40] : k2_xboole_0(A_40,k3_tarski(A_40)) = k3_tarski(k1_ordinal1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58,c_48011,c_50571])).

tff(c_60567,plain,(
    ! [A_1678,B_1679] :
      ( r1_tarski('#skF_7'(A_1678,B_1679),A_1678)
      | ~ v1_ordinal1(A_1678)
      | r1_tarski(k3_tarski(A_1678),B_1679) ) ),
    inference(resolution,[status(thm)],[c_39832,c_72])).

tff(c_60637,plain,(
    ! [A_1680] :
      ( ~ v1_ordinal1(A_1680)
      | r1_tarski(k3_tarski(A_1680),A_1680) ) ),
    inference(resolution,[status(thm)],[c_60567,c_60])).

tff(c_60653,plain,(
    ! [A_1680] :
      ( k2_xboole_0(k3_tarski(A_1680),A_1680) = A_1680
      | ~ v1_ordinal1(A_1680) ) ),
    inference(resolution,[status(thm)],[c_60637,c_30])).

tff(c_60721,plain,(
    ! [A_1681] :
      ( k3_tarski(k1_ordinal1(A_1681)) = A_1681
      | ~ v1_ordinal1(A_1681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50864,c_4,c_60653])).

tff(c_61001,plain,
    ( k3_tarski('#skF_10') = '#skF_11'
    | ~ v1_ordinal1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_41661,c_60721])).

tff(c_61027,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38870,c_38905,c_61001])).

tff(c_61029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41848,c_61027])).

tff(c_61031,plain,(
    k1_ordinal1('#skF_11') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_41646])).

tff(c_41496,plain,
    ( r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | k1_ordinal1('#skF_11') = '#skF_10'
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_41200,c_38900])).

tff(c_41610,plain,
    ( r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | k1_ordinal1('#skF_11') = '#skF_10'
    | ~ v3_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_41496])).

tff(c_61033,plain,
    ( r2_hidden('#skF_10',k1_ordinal1('#skF_11'))
    | k1_ordinal1('#skF_11') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41647,c_41610])).

tff(c_61034,plain,(
    r2_hidden('#skF_10',k1_ordinal1('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_61031,c_61033])).

tff(c_61039,plain,
    ( r1_tarski('#skF_10',k1_ordinal1('#skF_11'))
    | ~ v1_ordinal1(k1_ordinal1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_61034,c_72])).

tff(c_61051,plain,(
    r1_tarski('#skF_10',k1_ordinal1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41660,c_61039])).

tff(c_61066,plain,(
    k2_xboole_0('#skF_10',k1_ordinal1('#skF_11')) = k1_ordinal1('#skF_11') ),
    inference(resolution,[status(thm)],[c_61051,c_30])).

tff(c_39743,plain,(
    ! [B_1288] : k2_xboole_0('#skF_10',k3_tarski(B_1288)) = k3_tarski(k2_xboole_0('#skF_10',B_1288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38905,c_39696])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39346,plain,(
    ! [D_1257,A_1258,B_1259] :
      ( ~ r2_hidden(D_1257,A_1258)
      | r2_hidden(D_1257,k2_xboole_0(A_1258,B_1259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [B_64,A_63] :
      ( ~ r1_tarski(B_64,A_63)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63173,plain,(
    ! [A_1746,B_1747,D_1748] :
      ( ~ r1_tarski(k2_xboole_0(A_1746,B_1747),D_1748)
      | ~ r2_hidden(D_1748,A_1746) ) ),
    inference(resolution,[status(thm)],[c_39346,c_96])).

tff(c_63233,plain,(
    ! [A_1749,B_1750] : ~ r2_hidden(k2_xboole_0(A_1749,B_1750),A_1749) ),
    inference(resolution,[status(thm)],[c_28,c_63173])).

tff(c_63488,plain,(
    ! [B_1758] : ~ r2_hidden(k3_tarski(k2_xboole_0('#skF_10',B_1758)),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_39743,c_63233])).

tff(c_63492,plain,(
    ~ r2_hidden(k3_tarski(k1_ordinal1('#skF_11')),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_61066,c_63488])).

tff(c_82012,plain,
    ( ~ r2_hidden('#skF_11','#skF_10')
    | ~ v1_ordinal1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_81759,c_63492])).

tff(c_82139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38870,c_38853,c_82012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.18/11.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.18/11.29  
% 20.18/11.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.18/11.29  %$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_7 > #skF_5 > #skF_4
% 20.18/11.29  
% 20.18/11.29  %Foreground sorts:
% 20.18/11.29  
% 20.18/11.29  
% 20.18/11.29  %Background operators:
% 20.18/11.29  
% 20.18/11.29  
% 20.18/11.29  %Foreground operators:
% 20.18/11.29  tff('#skF_9', type, '#skF_9': $i > $i).
% 20.18/11.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.18/11.29  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 20.18/11.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.18/11.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.18/11.29  tff('#skF_11', type, '#skF_11': $i).
% 20.18/11.29  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 20.18/11.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.18/11.29  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 20.18/11.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.18/11.29  tff('#skF_8', type, '#skF_8': $i > $i).
% 20.18/11.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.18/11.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.18/11.29  tff('#skF_10', type, '#skF_10': $i).
% 20.18/11.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.18/11.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.18/11.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.18/11.29  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 20.18/11.29  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 20.18/11.29  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 20.18/11.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.18/11.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.18/11.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.18/11.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.18/11.29  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 20.18/11.29  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.18/11.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.18/11.29  
% 20.35/11.31  tff(f_67, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 20.35/11.31  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 20.35/11.31  tff(f_101, axiom, (![A]: (v4_ordinal1(A) <=> (A = k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 20.35/11.31  tff(f_155, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 20.35/11.31  tff(f_138, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 20.35/11.31  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 20.35/11.31  tff(f_103, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 20.35/11.31  tff(f_143, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 20.35/11.31  tff(f_112, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 20.35/11.31  tff(f_127, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 20.35/11.31  tff(f_88, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 20.35/11.31  tff(f_90, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 20.35/11.31  tff(f_73, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 20.35/11.31  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 20.35/11.31  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.35/11.31  tff(f_80, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 20.35/11.31  tff(f_97, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 20.35/11.31  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 20.35/11.31  tff(f_131, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 20.35/11.31  tff(f_106, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 20.35/11.31  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.35/11.31  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 20.35/11.31  tff(c_42, plain, (![C_34, A_19]: (r2_hidden(C_34, '#skF_6'(A_19, k3_tarski(A_19), C_34)) | ~r2_hidden(C_34, k3_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.35/11.31  tff(c_12132, plain, (![A_544, C_545]: (r2_hidden('#skF_6'(A_544, k3_tarski(A_544), C_545), A_544) | ~r2_hidden(C_545, k3_tarski(A_544)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.35/11.31  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 20.35/11.31  tff(c_38781, plain, (![A_1207, C_1208]: (~r2_hidden(A_1207, '#skF_6'(A_1207, k3_tarski(A_1207), C_1208)) | ~r2_hidden(C_1208, k3_tarski(A_1207)))), inference(resolution, [status(thm)], [c_12132, c_2])).
% 20.35/11.31  tff(c_38841, plain, (![A_19]: (~r2_hidden(A_19, k3_tarski(A_19)))), inference(resolution, [status(thm)], [c_42, c_38781])).
% 20.35/11.31  tff(c_140, plain, (![A_75]: (v4_ordinal1(A_75) | k3_tarski(A_75)!=A_75)), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.35/11.31  tff(c_104, plain, (v3_ordinal1('#skF_11') | ~v4_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.35/11.31  tff(c_120, plain, (~v4_ordinal1('#skF_10')), inference(splitLeft, [status(thm)], [c_104])).
% 20.35/11.31  tff(c_144, plain, (k3_tarski('#skF_10')!='#skF_10'), inference(resolution, [status(thm)], [c_140, c_120])).
% 20.35/11.31  tff(c_98, plain, (v3_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.35/11.31  tff(c_92, plain, (![A_61]: (~v3_ordinal1('#skF_9'(A_61)) | v3_ordinal1(k3_tarski(A_61)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 20.35/11.31  tff(c_114, plain, (![B_67]: (v4_ordinal1('#skF_10') | r2_hidden(k1_ordinal1(B_67), '#skF_10') | ~r2_hidden(B_67, '#skF_10') | ~v3_ordinal1(B_67))), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.35/11.31  tff(c_243, plain, (![B_67]: (r2_hidden(k1_ordinal1(B_67), '#skF_10') | ~r2_hidden(B_67, '#skF_10') | ~v3_ordinal1(B_67))), inference(negUnitSimplification, [status(thm)], [c_120, c_114])).
% 20.35/11.31  tff(c_443, plain, (![A_110, B_111]: (r1_tarski(A_110, k3_tarski(B_111)) | ~r2_hidden(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.35/11.31  tff(c_82, plain, (![A_53]: (r2_hidden(A_53, k1_ordinal1(A_53)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 20.35/11.31  tff(c_226, plain, (![B_87, A_88]: (~r1_tarski(B_87, A_88) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_143])).
% 20.35/11.31  tff(c_234, plain, (![A_53]: (~r1_tarski(k1_ordinal1(A_53), A_53))), inference(resolution, [status(thm)], [c_82, c_226])).
% 20.35/11.31  tff(c_464, plain, (![B_112]: (~r2_hidden(k1_ordinal1(k3_tarski(B_112)), B_112))), inference(resolution, [status(thm)], [c_443, c_234])).
% 20.35/11.31  tff(c_475, plain, (~r2_hidden(k3_tarski('#skF_10'), '#skF_10') | ~v3_ordinal1(k3_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_243, c_464])).
% 20.35/11.31  tff(c_528, plain, (~v3_ordinal1(k3_tarski('#skF_10'))), inference(splitLeft, [status(thm)], [c_475])).
% 20.35/11.31  tff(c_532, plain, (~v3_ordinal1('#skF_9'('#skF_10'))), inference(resolution, [status(thm)], [c_92, c_528])).
% 20.35/11.31  tff(c_94, plain, (![A_61]: (r2_hidden('#skF_9'(A_61), A_61) | v3_ordinal1(k3_tarski(A_61)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 20.35/11.31  tff(c_360, plain, (![A_106, B_107]: (v3_ordinal1(A_106) | ~r2_hidden(A_106, B_107) | ~v3_ordinal1(B_107))), inference(cnfTransformation, [status(thm)], [f_112])).
% 20.35/11.31  tff(c_4696, plain, (![A_281]: (v3_ordinal1('#skF_9'(A_281)) | ~v3_ordinal1(A_281) | v3_ordinal1(k3_tarski(A_281)))), inference(resolution, [status(thm)], [c_94, c_360])).
% 20.35/11.31  tff(c_4705, plain, (v3_ordinal1('#skF_9'('#skF_10')) | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_4696, c_528])).
% 20.35/11.31  tff(c_4737, plain, (v3_ordinal1('#skF_9'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_4705])).
% 20.35/11.31  tff(c_4739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_4737])).
% 20.35/11.31  tff(c_4741, plain, (v3_ordinal1(k3_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_475])).
% 20.35/11.31  tff(c_17440, plain, (![B_711, A_712]: (r2_hidden(B_711, A_712) | B_711=A_712 | r2_hidden(A_712, B_711) | ~v3_ordinal1(B_711) | ~v3_ordinal1(A_712))), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.35/11.31  tff(c_4740, plain, (~r2_hidden(k3_tarski('#skF_10'), '#skF_10')), inference(splitRight, [status(thm)], [c_475])).
% 20.35/11.31  tff(c_17588, plain, (k3_tarski('#skF_10')='#skF_10' | r2_hidden('#skF_10', k3_tarski('#skF_10')) | ~v3_ordinal1(k3_tarski('#skF_10')) | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_17440, c_4740])).
% 20.35/11.31  tff(c_17865, plain, (k3_tarski('#skF_10')='#skF_10' | r2_hidden('#skF_10', k3_tarski('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_4741, c_17588])).
% 20.35/11.31  tff(c_17866, plain, (r2_hidden('#skF_10', k3_tarski('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_144, c_17865])).
% 20.35/11.31  tff(c_38849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38841, c_17866])).
% 20.35/11.31  tff(c_38850, plain, (v3_ordinal1('#skF_11')), inference(splitRight, [status(thm)], [c_104])).
% 20.35/11.31  tff(c_38863, plain, (![A_1210]: (v1_ordinal1(A_1210) | ~v3_ordinal1(A_1210))), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.35/11.31  tff(c_38870, plain, (v1_ordinal1('#skF_11')), inference(resolution, [status(thm)], [c_38850, c_38863])).
% 20.35/11.31  tff(c_38851, plain, (v4_ordinal1('#skF_10')), inference(splitRight, [status(thm)], [c_104])).
% 20.35/11.31  tff(c_102, plain, (r2_hidden('#skF_11', '#skF_10') | ~v4_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.35/11.31  tff(c_38853, plain, (r2_hidden('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_38851, c_102])).
% 20.35/11.31  tff(c_70, plain, (![A_47]: (k2_xboole_0(A_47, k1_tarski(A_47))=k1_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_90])).
% 20.35/11.31  tff(c_58, plain, (![A_40]: (k3_tarski(k1_tarski(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.35/11.31  tff(c_39696, plain, (![A_1287, B_1288]: (k2_xboole_0(k3_tarski(A_1287), k3_tarski(B_1288))=k3_tarski(k2_xboole_0(A_1287, B_1288)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 20.35/11.31  tff(c_71079, plain, (![A_1901, A_1902]: (k3_tarski(k2_xboole_0(A_1901, k1_tarski(A_1902)))=k2_xboole_0(k3_tarski(A_1901), A_1902))), inference(superposition, [status(thm), theory('equality')], [c_58, c_39696])).
% 20.35/11.31  tff(c_71298, plain, (![A_1903]: (k2_xboole_0(k3_tarski(A_1903), A_1903)=k3_tarski(k1_ordinal1(A_1903)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_71079])).
% 20.35/11.31  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.35/11.31  tff(c_71525, plain, (![A_1903]: (k2_xboole_0(A_1903, k3_tarski(A_1903))=k3_tarski(k1_ordinal1(A_1903)))), inference(superposition, [status(thm), theory('equality')], [c_71298, c_4])).
% 20.35/11.31  tff(c_39832, plain, (![A_1292, B_1293]: (r2_hidden('#skF_7'(A_1292, B_1293), A_1292) | r1_tarski(k3_tarski(A_1292), B_1293))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.35/11.31  tff(c_72, plain, (![B_51, A_48]: (r1_tarski(B_51, A_48) | ~r2_hidden(B_51, A_48) | ~v1_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.35/11.31  tff(c_81616, plain, (![A_2031, B_2032]: (r1_tarski('#skF_7'(A_2031, B_2032), A_2031) | ~v1_ordinal1(A_2031) | r1_tarski(k3_tarski(A_2031), B_2032))), inference(resolution, [status(thm)], [c_39832, c_72])).
% 20.35/11.31  tff(c_60, plain, (![A_41, B_42]: (~r1_tarski('#skF_7'(A_41, B_42), B_42) | r1_tarski(k3_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.35/11.31  tff(c_81682, plain, (![A_2033]: (~v1_ordinal1(A_2033) | r1_tarski(k3_tarski(A_2033), A_2033))), inference(resolution, [status(thm)], [c_81616, c_60])).
% 20.35/11.31  tff(c_30, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.35/11.31  tff(c_81694, plain, (![A_2033]: (k2_xboole_0(k3_tarski(A_2033), A_2033)=A_2033 | ~v1_ordinal1(A_2033))), inference(resolution, [status(thm)], [c_81682, c_30])).
% 20.35/11.31  tff(c_81759, plain, (![A_2034]: (k3_tarski(k1_ordinal1(A_2034))=A_2034 | ~v1_ordinal1(A_2034))), inference(demodulation, [status(thm), theory('equality')], [c_71525, c_4, c_81694])).
% 20.35/11.31  tff(c_90, plain, (![A_60]: (v3_ordinal1(k1_ordinal1(A_60)) | ~v3_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_131])).
% 20.35/11.31  tff(c_41200, plain, (![B_1331, A_1332]: (r2_hidden(B_1331, A_1332) | B_1331=A_1332 | r2_hidden(A_1332, B_1331) | ~v3_ordinal1(B_1331) | ~v3_ordinal1(A_1332))), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.35/11.31  tff(c_100, plain, (~r2_hidden(k1_ordinal1('#skF_11'), '#skF_10') | ~v4_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_155])).
% 20.35/11.31  tff(c_38900, plain, (~r2_hidden(k1_ordinal1('#skF_11'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_38851, c_100])).
% 20.35/11.31  tff(c_41348, plain, (k1_ordinal1('#skF_11')='#skF_10' | r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | ~v3_ordinal1(k1_ordinal1('#skF_11')) | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_41200, c_38900])).
% 20.35/11.31  tff(c_41553, plain, (k1_ordinal1('#skF_11')='#skF_10' | r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | ~v3_ordinal1(k1_ordinal1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_41348])).
% 20.35/11.31  tff(c_41638, plain, (~v3_ordinal1(k1_ordinal1('#skF_11'))), inference(splitLeft, [status(thm)], [c_41553])).
% 20.35/11.31  tff(c_41641, plain, (~v3_ordinal1('#skF_11')), inference(resolution, [status(thm)], [c_90, c_41638])).
% 20.35/11.31  tff(c_41645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38850, c_41641])).
% 20.35/11.31  tff(c_41647, plain, (v3_ordinal1(k1_ordinal1('#skF_11'))), inference(splitRight, [status(thm)], [c_41553])).
% 20.35/11.31  tff(c_68, plain, (![A_46]: (v1_ordinal1(A_46) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.35/11.31  tff(c_41660, plain, (v1_ordinal1(k1_ordinal1('#skF_11'))), inference(resolution, [status(thm)], [c_41647, c_68])).
% 20.35/11.31  tff(c_41646, plain, (r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | k1_ordinal1('#skF_11')='#skF_10'), inference(splitRight, [status(thm)], [c_41553])).
% 20.35/11.31  tff(c_41661, plain, (k1_ordinal1('#skF_11')='#skF_10'), inference(splitLeft, [status(thm)], [c_41646])).
% 20.35/11.31  tff(c_84, plain, (![A_54]: (k1_ordinal1(A_54)!=A_54)), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.35/11.31  tff(c_41848, plain, ('#skF_11'!='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_41661, c_84])).
% 20.35/11.31  tff(c_38901, plain, (![A_1214]: (k3_tarski(A_1214)=A_1214 | ~v4_ordinal1(A_1214))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.35/11.31  tff(c_38905, plain, (k3_tarski('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_38851, c_38901])).
% 20.35/11.31  tff(c_47836, plain, (![A_1506, B_1507]: (k3_tarski(k2_xboole_0(k1_tarski(A_1506), B_1507))=k2_xboole_0(A_1506, k3_tarski(B_1507)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_39696])).
% 20.35/11.31  tff(c_47987, plain, (![A_1506]: (k2_xboole_0(A_1506, k3_tarski(k1_tarski(k1_tarski(A_1506))))=k3_tarski(k1_ordinal1(k1_tarski(A_1506))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_47836])).
% 20.35/11.31  tff(c_48011, plain, (![A_1506]: (k3_tarski(k1_ordinal1(k1_tarski(A_1506)))=k1_ordinal1(A_1506))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_47987])).
% 20.35/11.31  tff(c_50332, plain, (![A_1545, A_1546]: (k3_tarski(k2_xboole_0(A_1545, k1_tarski(A_1546)))=k2_xboole_0(k3_tarski(A_1545), A_1546))), inference(superposition, [status(thm), theory('equality')], [c_58, c_39696])).
% 20.35/11.31  tff(c_50564, plain, (![A_1547]: (k2_xboole_0(k3_tarski(A_1547), A_1547)=k3_tarski(k1_ordinal1(A_1547)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_50332])).
% 20.35/11.31  tff(c_39752, plain, (![A_1287, A_40]: (k3_tarski(k2_xboole_0(A_1287, k1_tarski(A_40)))=k2_xboole_0(k3_tarski(A_1287), A_40))), inference(superposition, [status(thm), theory('equality')], [c_58, c_39696])).
% 20.35/11.31  tff(c_50571, plain, (![A_40]: (k2_xboole_0(k3_tarski(k3_tarski(k1_tarski(A_40))), A_40)=k3_tarski(k3_tarski(k1_ordinal1(k1_tarski(A_40)))))), inference(superposition, [status(thm), theory('equality')], [c_50564, c_39752])).
% 20.35/11.31  tff(c_50864, plain, (![A_40]: (k2_xboole_0(A_40, k3_tarski(A_40))=k3_tarski(k1_ordinal1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58, c_48011, c_50571])).
% 20.35/11.31  tff(c_60567, plain, (![A_1678, B_1679]: (r1_tarski('#skF_7'(A_1678, B_1679), A_1678) | ~v1_ordinal1(A_1678) | r1_tarski(k3_tarski(A_1678), B_1679))), inference(resolution, [status(thm)], [c_39832, c_72])).
% 20.35/11.31  tff(c_60637, plain, (![A_1680]: (~v1_ordinal1(A_1680) | r1_tarski(k3_tarski(A_1680), A_1680))), inference(resolution, [status(thm)], [c_60567, c_60])).
% 20.35/11.31  tff(c_60653, plain, (![A_1680]: (k2_xboole_0(k3_tarski(A_1680), A_1680)=A_1680 | ~v1_ordinal1(A_1680))), inference(resolution, [status(thm)], [c_60637, c_30])).
% 20.35/11.31  tff(c_60721, plain, (![A_1681]: (k3_tarski(k1_ordinal1(A_1681))=A_1681 | ~v1_ordinal1(A_1681))), inference(demodulation, [status(thm), theory('equality')], [c_50864, c_4, c_60653])).
% 20.35/11.31  tff(c_61001, plain, (k3_tarski('#skF_10')='#skF_11' | ~v1_ordinal1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_41661, c_60721])).
% 20.35/11.31  tff(c_61027, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_38870, c_38905, c_61001])).
% 20.35/11.31  tff(c_61029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41848, c_61027])).
% 20.35/11.31  tff(c_61031, plain, (k1_ordinal1('#skF_11')!='#skF_10'), inference(splitRight, [status(thm)], [c_41646])).
% 20.35/11.31  tff(c_41496, plain, (r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | k1_ordinal1('#skF_11')='#skF_10' | ~v3_ordinal1('#skF_10') | ~v3_ordinal1(k1_ordinal1('#skF_11'))), inference(resolution, [status(thm)], [c_41200, c_38900])).
% 20.35/11.31  tff(c_41610, plain, (r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | k1_ordinal1('#skF_11')='#skF_10' | ~v3_ordinal1(k1_ordinal1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_41496])).
% 20.35/11.31  tff(c_61033, plain, (r2_hidden('#skF_10', k1_ordinal1('#skF_11')) | k1_ordinal1('#skF_11')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_41647, c_41610])).
% 20.35/11.31  tff(c_61034, plain, (r2_hidden('#skF_10', k1_ordinal1('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_61031, c_61033])).
% 20.35/11.31  tff(c_61039, plain, (r1_tarski('#skF_10', k1_ordinal1('#skF_11')) | ~v1_ordinal1(k1_ordinal1('#skF_11'))), inference(resolution, [status(thm)], [c_61034, c_72])).
% 20.35/11.31  tff(c_61051, plain, (r1_tarski('#skF_10', k1_ordinal1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_41660, c_61039])).
% 20.35/11.31  tff(c_61066, plain, (k2_xboole_0('#skF_10', k1_ordinal1('#skF_11'))=k1_ordinal1('#skF_11')), inference(resolution, [status(thm)], [c_61051, c_30])).
% 20.35/11.31  tff(c_39743, plain, (![B_1288]: (k2_xboole_0('#skF_10', k3_tarski(B_1288))=k3_tarski(k2_xboole_0('#skF_10', B_1288)))), inference(superposition, [status(thm), theory('equality')], [c_38905, c_39696])).
% 20.35/11.31  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.35/11.31  tff(c_39346, plain, (![D_1257, A_1258, B_1259]: (~r2_hidden(D_1257, A_1258) | r2_hidden(D_1257, k2_xboole_0(A_1258, B_1259)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.35/11.31  tff(c_96, plain, (![B_64, A_63]: (~r1_tarski(B_64, A_63) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_143])).
% 20.35/11.31  tff(c_63173, plain, (![A_1746, B_1747, D_1748]: (~r1_tarski(k2_xboole_0(A_1746, B_1747), D_1748) | ~r2_hidden(D_1748, A_1746))), inference(resolution, [status(thm)], [c_39346, c_96])).
% 20.35/11.31  tff(c_63233, plain, (![A_1749, B_1750]: (~r2_hidden(k2_xboole_0(A_1749, B_1750), A_1749))), inference(resolution, [status(thm)], [c_28, c_63173])).
% 20.35/11.31  tff(c_63488, plain, (![B_1758]: (~r2_hidden(k3_tarski(k2_xboole_0('#skF_10', B_1758)), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_39743, c_63233])).
% 20.35/11.31  tff(c_63492, plain, (~r2_hidden(k3_tarski(k1_ordinal1('#skF_11')), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_61066, c_63488])).
% 20.35/11.31  tff(c_82012, plain, (~r2_hidden('#skF_11', '#skF_10') | ~v1_ordinal1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_81759, c_63492])).
% 20.35/11.31  tff(c_82139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38870, c_38853, c_82012])).
% 20.35/11.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.35/11.31  
% 20.35/11.31  Inference rules
% 20.35/11.31  ----------------------
% 20.35/11.31  #Ref     : 0
% 20.35/11.31  #Sup     : 19242
% 20.35/11.31  #Fact    : 54
% 20.35/11.31  #Define  : 0
% 20.35/11.31  #Split   : 48
% 20.35/11.31  #Chain   : 0
% 20.35/11.31  #Close   : 0
% 20.35/11.31  
% 20.35/11.31  Ordering : KBO
% 20.35/11.31  
% 20.35/11.31  Simplification rules
% 20.35/11.31  ----------------------
% 20.35/11.31  #Subsume      : 6555
% 20.35/11.31  #Demod        : 5777
% 20.35/11.31  #Tautology    : 1448
% 20.35/11.31  #SimpNegUnit  : 206
% 20.35/11.31  #BackRed      : 200
% 20.35/11.31  
% 20.35/11.31  #Partial instantiations: 0
% 20.35/11.31  #Strategies tried      : 1
% 20.35/11.31  
% 20.35/11.31  Timing (in seconds)
% 20.35/11.31  ----------------------
% 20.35/11.32  Preprocessing        : 0.36
% 20.35/11.32  Parsing              : 0.17
% 20.35/11.32  CNF conversion       : 0.03
% 20.35/11.32  Main loop            : 10.04
% 20.35/11.32  Inferencing          : 1.72
% 20.35/11.32  Reduction            : 3.95
% 20.35/11.32  Demodulation         : 2.68
% 20.35/11.32  BG Simplification    : 0.22
% 20.35/11.32  Subsumption          : 3.45
% 20.35/11.32  Abstraction          : 0.28
% 20.35/11.32  MUC search           : 0.00
% 20.35/11.32  Cooper               : 0.00
% 20.35/11.32  Total                : 10.44
% 20.35/11.32  Index Insertion      : 0.00
% 20.35/11.32  Index Deletion       : 0.00
% 20.35/11.32  Index Matching       : 0.00
% 20.35/11.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
