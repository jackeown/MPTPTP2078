%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 473 expanded)
%              Number of leaves         :   27 ( 171 expanded)
%              Depth                    :   25
%              Number of atoms          :  242 ( 839 expanded)
%              Number of equality atoms :   71 ( 251 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_36,plain,
    ( k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    k5_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_78,plain,(
    k5_relat_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_60])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_32])).

tff(c_124,plain,(
    ! [A_28] :
      ( k1_relat_1(k4_relat_1(A_28)) = k2_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_227,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(k2_relat_1(A_40))
      | ~ v1_relat_1(k4_relat_1(A_40))
      | v1_xboole_0(k4_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_20])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_239,plain,(
    ! [A_41] :
      ( k4_relat_1(A_41) = '#skF_1'
      | ~ v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_relat_1(k4_relat_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_227,c_61])).

tff(c_248,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_239])).

tff(c_252,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4,c_248])).

tff(c_253,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_256,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_256])).

tff(c_261,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_30,plain,(
    ! [B_17,A_15] :
      ( k5_relat_1(k4_relat_1(B_17),k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_272,plain,(
    ! [B_17] :
      ( k5_relat_1(k4_relat_1(B_17),'#skF_1') = k4_relat_1(k5_relat_1('#skF_1',B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_30])).

tff(c_326,plain,(
    ! [B_44] :
      ( k5_relat_1(k4_relat_1(B_44),'#skF_1') = k4_relat_1(k5_relat_1('#skF_1',B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_272])).

tff(c_163,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_34,B_35)),k2_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_171,plain,(
    ! [A_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_34,'#skF_1')),'#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_163])).

tff(c_175,plain,(
    ! [A_36] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_36,'#skF_1')),'#skF_1')
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_171])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_140,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_140])).

tff(c_181,plain,(
    ! [A_36] :
      ( k2_relat_1(k5_relat_1(A_36,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_175,c_145])).

tff(c_646,plain,(
    ! [B_52] :
      ( k2_relat_1(k4_relat_1(k5_relat_1('#skF_1',B_52))) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_181])).

tff(c_1391,plain,(
    ! [B_68] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_68)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k5_relat_1('#skF_1',B_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_646])).

tff(c_1408,plain,(
    ! [B_8] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_8)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_1391])).

tff(c_1418,plain,(
    ! [B_69] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_69)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1408])).

tff(c_1461,plain,(
    ! [A_70] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_70)) = '#skF_1'
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_16,c_1418])).

tff(c_1473,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1('#skF_1',A_70))
      | v1_xboole_0(k5_relat_1('#skF_1',A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_20])).

tff(c_1489,plain,(
    ! [A_71] :
      ( ~ v1_relat_1(k5_relat_1('#skF_1',A_71))
      | v1_xboole_0(k5_relat_1('#skF_1',A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1473])).

tff(c_1584,plain,(
    ! [A_74] :
      ( k5_relat_1('#skF_1',A_74) = '#skF_1'
      | ~ v1_relat_1(k5_relat_1('#skF_1',A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_1489,c_61])).

tff(c_1601,plain,(
    ! [B_8] :
      ( k5_relat_1('#skF_1',B_8) = '#skF_1'
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_1584])).

tff(c_1611,plain,(
    ! [B_75] :
      ( k5_relat_1('#skF_1',B_75) = '#skF_1'
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1601])).

tff(c_1638,plain,(
    k5_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_1611])).

tff(c_1651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1638])).

tff(c_1652,plain,(
    k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1676,plain,(
    k5_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_1652])).

tff(c_1657,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_32])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1716,plain,(
    ! [A_81] :
      ( ~ v1_xboole_0(k1_relat_1(A_81))
      | ~ v1_relat_1(A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1835,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(k2_relat_1(A_94))
      | ~ v1_relat_1(k4_relat_1(A_94))
      | v1_xboole_0(k4_relat_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1716])).

tff(c_1654,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_1847,plain,(
    ! [A_95] :
      ( k4_relat_1(A_95) = '#skF_1'
      | ~ v1_xboole_0(k2_relat_1(A_95))
      | ~ v1_relat_1(k4_relat_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_1835,c_1654])).

tff(c_1856,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_1847])).

tff(c_1860,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4,c_1856])).

tff(c_1861,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_1864,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1861])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1864])).

tff(c_1869,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_1880,plain,(
    ! [B_17] :
      ( k5_relat_1(k4_relat_1(B_17),'#skF_1') = k4_relat_1(k5_relat_1('#skF_1',B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_30])).

tff(c_2115,plain,(
    ! [B_101] :
      ( k5_relat_1(k4_relat_1(B_101),'#skF_1') = k4_relat_1(k5_relat_1('#skF_1',B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1880])).

tff(c_1766,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_88,B_89)),k2_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1774,plain,(
    ! [A_88] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_88,'#skF_1')),'#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_1766])).

tff(c_1804,plain,(
    ! [A_92] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_92,'#skF_1')),'#skF_1')
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1774])).

tff(c_1655,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_1737,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(B_83,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1742,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1655,c_1737])).

tff(c_1810,plain,(
    ! [A_92] :
      ( k2_relat_1(k5_relat_1(A_92,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_1804,c_1742])).

tff(c_2176,plain,(
    ! [B_104] :
      ( k2_relat_1(k4_relat_1(k5_relat_1('#skF_1',B_104))) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2115,c_1810])).

tff(c_2951,plain,(
    ! [B_120] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_120)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(k5_relat_1('#skF_1',B_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2176])).

tff(c_2968,plain,(
    ! [B_8] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_8)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_2951])).

tff(c_2983,plain,(
    ! [B_121] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_121)) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2968])).

tff(c_3073,plain,(
    ! [A_124] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_124)) = '#skF_1'
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_16,c_2983])).

tff(c_3085,plain,(
    ! [A_124] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1('#skF_1',A_124))
      | v1_xboole_0(k5_relat_1('#skF_1',A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_20])).

tff(c_3106,plain,(
    ! [A_125] :
      ( ~ v1_relat_1(k5_relat_1('#skF_1',A_125))
      | v1_xboole_0(k5_relat_1('#skF_1',A_125))
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3085])).

tff(c_3128,plain,(
    ! [A_126] :
      ( k5_relat_1('#skF_1',A_126) = '#skF_1'
      | ~ v1_relat_1(k5_relat_1('#skF_1',A_126))
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_3106,c_1654])).

tff(c_3145,plain,(
    ! [B_8] :
      ( k5_relat_1('#skF_1',B_8) = '#skF_1'
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_3128])).

tff(c_3160,plain,(
    ! [B_127] :
      ( k5_relat_1('#skF_1',B_127) = '#skF_1'
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3145])).

tff(c_3199,plain,(
    ! [A_128] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_128)) = '#skF_1'
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_16,c_3160])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1783,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(k4_relat_1(B_90),k4_relat_1(A_91)) = k4_relat_1(k5_relat_1(A_91,B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1798,plain,(
    ! [A_91,A_10] :
      ( k4_relat_1(k5_relat_1(A_91,k4_relat_1(A_10))) = k5_relat_1(A_10,k4_relat_1(A_91))
      | ~ v1_relat_1(k4_relat_1(A_10))
      | ~ v1_relat_1(A_91)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1783])).

tff(c_3214,plain,(
    ! [A_128] :
      ( k5_relat_1(A_128,k4_relat_1('#skF_1')) = k4_relat_1('#skF_1')
      | ~ v1_relat_1(k4_relat_1(A_128))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3199,c_1798])).

tff(c_3302,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_129))
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1869,c_1869,c_3214])).

tff(c_3433,plain,(
    ! [A_132] :
      ( k5_relat_1(A_132,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_16,c_3302])).

tff(c_3460,plain,(
    k5_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_3433])).

tff(c_3473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1676,c_3460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:57:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.91  
% 4.87/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.91  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.87/1.91  
% 4.87/1.91  %Foreground sorts:
% 4.87/1.91  
% 4.87/1.91  
% 4.87/1.91  %Background operators:
% 4.87/1.91  
% 4.87/1.91  
% 4.87/1.91  %Foreground operators:
% 4.87/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/1.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.87/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.87/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.87/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.87/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.87/1.91  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.87/1.91  
% 4.87/1.93  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.87/1.93  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.87/1.93  tff(f_95, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 4.87/1.93  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.87/1.93  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.87/1.93  tff(f_47, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.87/1.93  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.87/1.93  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.87/1.93  tff(f_61, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 4.87/1.93  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 4.87/1.93  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 4.87/1.93  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.87/1.93  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.87/1.93  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.87/1.93  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.93  tff(c_55, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.87/1.93  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_55])).
% 4.87/1.93  tff(c_36, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.87/1.93  tff(c_60, plain, (k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 4.87/1.93  tff(c_78, plain, (k5_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_60])).
% 4.87/1.93  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.87/1.93  tff(c_50, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/1.93  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_50])).
% 4.87/1.93  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.87/1.93  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.87/1.93  tff(c_24, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.87/1.93  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/1.93  tff(c_64, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_32])).
% 4.87/1.93  tff(c_124, plain, (![A_28]: (k1_relat_1(k4_relat_1(A_28))=k2_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.87/1.93  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.87/1.93  tff(c_227, plain, (![A_40]: (~v1_xboole_0(k2_relat_1(A_40)) | ~v1_relat_1(k4_relat_1(A_40)) | v1_xboole_0(k4_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_124, c_20])).
% 4.87/1.93  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.87/1.93  tff(c_61, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 4.87/1.93  tff(c_239, plain, (![A_41]: (k4_relat_1(A_41)='#skF_1' | ~v1_xboole_0(k2_relat_1(A_41)) | ~v1_relat_1(k4_relat_1(A_41)) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_227, c_61])).
% 4.87/1.93  tff(c_248, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_239])).
% 4.87/1.93  tff(c_252, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4, c_248])).
% 4.87/1.93  tff(c_253, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_252])).
% 4.87/1.93  tff(c_256, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_253])).
% 4.87/1.93  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_256])).
% 4.87/1.93  tff(c_261, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_252])).
% 4.87/1.93  tff(c_30, plain, (![B_17, A_15]: (k5_relat_1(k4_relat_1(B_17), k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.87/1.93  tff(c_272, plain, (![B_17]: (k5_relat_1(k4_relat_1(B_17), '#skF_1')=k4_relat_1(k5_relat_1('#skF_1', B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_30])).
% 4.87/1.93  tff(c_326, plain, (![B_44]: (k5_relat_1(k4_relat_1(B_44), '#skF_1')=k4_relat_1(k5_relat_1('#skF_1', B_44)) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_272])).
% 4.87/1.93  tff(c_163, plain, (![A_34, B_35]: (r1_tarski(k2_relat_1(k5_relat_1(A_34, B_35)), k2_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/1.93  tff(c_171, plain, (![A_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_34, '#skF_1')), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_64, c_163])).
% 4.87/1.93  tff(c_175, plain, (![A_36]: (r1_tarski(k2_relat_1(k5_relat_1(A_36, '#skF_1')), '#skF_1') | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_171])).
% 4.87/1.93  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.87/1.93  tff(c_62, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 4.87/1.93  tff(c_140, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/1.93  tff(c_145, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_140])).
% 4.87/1.93  tff(c_181, plain, (![A_36]: (k2_relat_1(k5_relat_1(A_36, '#skF_1'))='#skF_1' | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_175, c_145])).
% 4.87/1.93  tff(c_646, plain, (![B_52]: (k2_relat_1(k4_relat_1(k5_relat_1('#skF_1', B_52)))='#skF_1' | ~v1_relat_1(k4_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_326, c_181])).
% 4.87/1.93  tff(c_1391, plain, (![B_68]: (k1_relat_1(k5_relat_1('#skF_1', B_68))='#skF_1' | ~v1_relat_1(k4_relat_1(B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(k5_relat_1('#skF_1', B_68)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_646])).
% 4.87/1.93  tff(c_1408, plain, (![B_8]: (k1_relat_1(k5_relat_1('#skF_1', B_8))='#skF_1' | ~v1_relat_1(k4_relat_1(B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_1391])).
% 4.87/1.93  tff(c_1418, plain, (![B_69]: (k1_relat_1(k5_relat_1('#skF_1', B_69))='#skF_1' | ~v1_relat_1(k4_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1408])).
% 4.87/1.93  tff(c_1461, plain, (![A_70]: (k1_relat_1(k5_relat_1('#skF_1', A_70))='#skF_1' | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_16, c_1418])).
% 4.87/1.93  tff(c_1473, plain, (![A_70]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', A_70)) | v1_xboole_0(k5_relat_1('#skF_1', A_70)) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_1461, c_20])).
% 4.87/1.93  tff(c_1489, plain, (![A_71]: (~v1_relat_1(k5_relat_1('#skF_1', A_71)) | v1_xboole_0(k5_relat_1('#skF_1', A_71)) | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1473])).
% 4.87/1.93  tff(c_1584, plain, (![A_74]: (k5_relat_1('#skF_1', A_74)='#skF_1' | ~v1_relat_1(k5_relat_1('#skF_1', A_74)) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_1489, c_61])).
% 4.87/1.93  tff(c_1601, plain, (![B_8]: (k5_relat_1('#skF_1', B_8)='#skF_1' | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_1584])).
% 4.87/1.93  tff(c_1611, plain, (![B_75]: (k5_relat_1('#skF_1', B_75)='#skF_1' | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1601])).
% 4.87/1.93  tff(c_1638, plain, (k5_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_1611])).
% 4.87/1.93  tff(c_1651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1638])).
% 4.87/1.93  tff(c_1652, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.87/1.93  tff(c_1676, plain, (k5_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_1652])).
% 4.87/1.93  tff(c_1657, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_32])).
% 4.87/1.93  tff(c_26, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.87/1.93  tff(c_1716, plain, (![A_81]: (~v1_xboole_0(k1_relat_1(A_81)) | ~v1_relat_1(A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.87/1.93  tff(c_1835, plain, (![A_94]: (~v1_xboole_0(k2_relat_1(A_94)) | ~v1_relat_1(k4_relat_1(A_94)) | v1_xboole_0(k4_relat_1(A_94)) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1716])).
% 4.87/1.93  tff(c_1654, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 4.87/1.93  tff(c_1847, plain, (![A_95]: (k4_relat_1(A_95)='#skF_1' | ~v1_xboole_0(k2_relat_1(A_95)) | ~v1_relat_1(k4_relat_1(A_95)) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_1835, c_1654])).
% 4.87/1.93  tff(c_1856, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_1847])).
% 4.87/1.93  tff(c_1860, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4, c_1856])).
% 4.87/1.93  tff(c_1861, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1860])).
% 4.87/1.93  tff(c_1864, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1861])).
% 4.87/1.93  tff(c_1868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1864])).
% 4.87/1.93  tff(c_1869, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_1860])).
% 4.87/1.93  tff(c_1880, plain, (![B_17]: (k5_relat_1(k4_relat_1(B_17), '#skF_1')=k4_relat_1(k5_relat_1('#skF_1', B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1869, c_30])).
% 4.87/1.93  tff(c_2115, plain, (![B_101]: (k5_relat_1(k4_relat_1(B_101), '#skF_1')=k4_relat_1(k5_relat_1('#skF_1', B_101)) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1880])).
% 4.87/1.93  tff(c_1766, plain, (![A_88, B_89]: (r1_tarski(k2_relat_1(k5_relat_1(A_88, B_89)), k2_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/1.93  tff(c_1774, plain, (![A_88]: (r1_tarski(k2_relat_1(k5_relat_1(A_88, '#skF_1')), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_1657, c_1766])).
% 4.87/1.93  tff(c_1804, plain, (![A_92]: (r1_tarski(k2_relat_1(k5_relat_1(A_92, '#skF_1')), '#skF_1') | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1774])).
% 4.87/1.93  tff(c_1655, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 4.87/1.93  tff(c_1737, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(B_83, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/1.93  tff(c_1742, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_1655, c_1737])).
% 4.87/1.93  tff(c_1810, plain, (![A_92]: (k2_relat_1(k5_relat_1(A_92, '#skF_1'))='#skF_1' | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_1804, c_1742])).
% 4.87/1.93  tff(c_2176, plain, (![B_104]: (k2_relat_1(k4_relat_1(k5_relat_1('#skF_1', B_104)))='#skF_1' | ~v1_relat_1(k4_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_2115, c_1810])).
% 4.87/1.93  tff(c_2951, plain, (![B_120]: (k1_relat_1(k5_relat_1('#skF_1', B_120))='#skF_1' | ~v1_relat_1(k4_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(k5_relat_1('#skF_1', B_120)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2176])).
% 4.87/1.93  tff(c_2968, plain, (![B_8]: (k1_relat_1(k5_relat_1('#skF_1', B_8))='#skF_1' | ~v1_relat_1(k4_relat_1(B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_2951])).
% 4.87/1.93  tff(c_2983, plain, (![B_121]: (k1_relat_1(k5_relat_1('#skF_1', B_121))='#skF_1' | ~v1_relat_1(k4_relat_1(B_121)) | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2968])).
% 4.87/1.93  tff(c_3073, plain, (![A_124]: (k1_relat_1(k5_relat_1('#skF_1', A_124))='#skF_1' | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_16, c_2983])).
% 4.87/1.93  tff(c_3085, plain, (![A_124]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', A_124)) | v1_xboole_0(k5_relat_1('#skF_1', A_124)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_20])).
% 4.87/1.93  tff(c_3106, plain, (![A_125]: (~v1_relat_1(k5_relat_1('#skF_1', A_125)) | v1_xboole_0(k5_relat_1('#skF_1', A_125)) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3085])).
% 4.87/1.93  tff(c_3128, plain, (![A_126]: (k5_relat_1('#skF_1', A_126)='#skF_1' | ~v1_relat_1(k5_relat_1('#skF_1', A_126)) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_3106, c_1654])).
% 4.87/1.93  tff(c_3145, plain, (![B_8]: (k5_relat_1('#skF_1', B_8)='#skF_1' | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_3128])).
% 4.87/1.93  tff(c_3160, plain, (![B_127]: (k5_relat_1('#skF_1', B_127)='#skF_1' | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3145])).
% 4.87/1.93  tff(c_3199, plain, (![A_128]: (k5_relat_1('#skF_1', k4_relat_1(A_128))='#skF_1' | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_16, c_3160])).
% 4.87/1.93  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.87/1.93  tff(c_1783, plain, (![B_90, A_91]: (k5_relat_1(k4_relat_1(B_90), k4_relat_1(A_91))=k4_relat_1(k5_relat_1(A_91, B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.87/1.93  tff(c_1798, plain, (![A_91, A_10]: (k4_relat_1(k5_relat_1(A_91, k4_relat_1(A_10)))=k5_relat_1(A_10, k4_relat_1(A_91)) | ~v1_relat_1(k4_relat_1(A_10)) | ~v1_relat_1(A_91) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1783])).
% 4.87/1.93  tff(c_3214, plain, (![A_128]: (k5_relat_1(A_128, k4_relat_1('#skF_1'))=k4_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1(A_128)) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_3199, c_1798])).
% 4.87/1.93  tff(c_3302, plain, (![A_129]: (k5_relat_1(A_129, '#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1(A_129)) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1869, c_1869, c_3214])).
% 4.87/1.93  tff(c_3433, plain, (![A_132]: (k5_relat_1(A_132, '#skF_1')='#skF_1' | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_16, c_3302])).
% 4.87/1.93  tff(c_3460, plain, (k5_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_3433])).
% 4.87/1.93  tff(c_3473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1676, c_3460])).
% 4.87/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.93  
% 4.87/1.93  Inference rules
% 4.87/1.93  ----------------------
% 4.87/1.93  #Ref     : 0
% 4.87/1.93  #Sup     : 869
% 4.87/1.93  #Fact    : 0
% 4.87/1.93  #Define  : 0
% 4.87/1.93  #Split   : 4
% 4.87/1.93  #Chain   : 0
% 4.87/1.93  #Close   : 0
% 4.87/1.93  
% 4.87/1.93  Ordering : KBO
% 4.87/1.93  
% 4.87/1.93  Simplification rules
% 4.87/1.93  ----------------------
% 4.87/1.93  #Subsume      : 105
% 4.87/1.93  #Demod        : 906
% 4.87/1.93  #Tautology    : 286
% 4.87/1.93  #SimpNegUnit  : 2
% 4.87/1.93  #BackRed      : 18
% 4.87/1.93  
% 4.87/1.93  #Partial instantiations: 0
% 4.87/1.93  #Strategies tried      : 1
% 4.87/1.93  
% 4.87/1.93  Timing (in seconds)
% 4.87/1.93  ----------------------
% 4.87/1.94  Preprocessing        : 0.31
% 4.87/1.94  Parsing              : 0.19
% 4.87/1.94  CNF conversion       : 0.02
% 4.87/1.94  Main loop            : 0.84
% 4.87/1.94  Inferencing          : 0.28
% 4.87/1.94  Reduction            : 0.27
% 4.87/1.94  Demodulation         : 0.20
% 4.87/1.94  BG Simplification    : 0.04
% 4.87/1.94  Subsumption          : 0.19
% 4.87/1.94  Abstraction          : 0.04
% 4.87/1.94  MUC search           : 0.00
% 4.87/1.94  Cooper               : 0.00
% 4.87/1.94  Total                : 1.19
% 4.87/1.94  Index Insertion      : 0.00
% 4.87/1.94  Index Deletion       : 0.00
% 4.87/1.94  Index Matching       : 0.00
% 4.87/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
