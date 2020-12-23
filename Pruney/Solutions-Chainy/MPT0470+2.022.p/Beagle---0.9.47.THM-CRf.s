%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 473 expanded)
%              Number of leaves         :   27 ( 171 expanded)
%              Depth                    :   25
%              Number of atoms          :  239 ( 839 expanded)
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

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
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

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

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_34])).

tff(c_112,plain,(
    ! [A_27] :
      ( k2_relat_1(k4_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_227,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(k1_relat_1(A_40))
      | ~ v1_relat_1(k4_relat_1(A_40))
      | v1_xboole_0(k4_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_20])).

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
      | ~ v1_xboole_0(k1_relat_1(A_41))
      | ~ v1_relat_1(k4_relat_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_227,c_61])).

tff(c_248,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_239])).

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

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [B_17,A_15] :
      ( k5_relat_1(k4_relat_1(B_17),k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_269,plain,(
    ! [A_15] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_30])).

tff(c_488,plain,(
    ! [A_47] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_47)) = k4_relat_1(k5_relat_1(A_47,'#skF_1'))
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_269])).

tff(c_163,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_34,B_35)),k1_relat_1(A_34))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_171,plain,(
    ! [B_35] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_35)),'#skF_1')
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_163])).

tff(c_175,plain,(
    ! [B_36] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_36)),'#skF_1')
      | ~ v1_relat_1(B_36) ) ),
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
    ! [B_36] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_36)) = '#skF_1'
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_175,c_145])).

tff(c_544,plain,(
    ! [A_50] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_50,'#skF_1'))) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_181])).

tff(c_1299,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(A_66,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_66))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(k5_relat_1(A_66,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_544])).

tff(c_1316,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(A_7,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_1299])).

tff(c_1326,plain,(
    ! [A_67] :
      ( k2_relat_1(k5_relat_1(A_67,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1316])).

tff(c_1411,plain,(
    ! [A_70] :
      ( k2_relat_1(k5_relat_1(A_70,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_16,c_1326])).

tff(c_1423,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1(A_70,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_70,'#skF_1'))
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_20])).

tff(c_1439,plain,(
    ! [A_71] :
      ( ~ v1_relat_1(k5_relat_1(A_71,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_71,'#skF_1'))
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1423])).

tff(c_1456,plain,(
    ! [A_72] :
      ( k5_relat_1(A_72,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_72,'#skF_1'))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_1439,c_61])).

tff(c_1473,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_1456])).

tff(c_1483,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1473])).

tff(c_1580,plain,(
    ! [A_74] :
      ( k5_relat_1(k4_relat_1(A_74),'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_16,c_1483])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_206,plain,(
    ! [B_38,A_39] :
      ( k5_relat_1(k4_relat_1(B_38),k4_relat_1(A_39)) = k4_relat_1(k5_relat_1(A_39,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_224,plain,(
    ! [A_10,B_38] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_10),B_38)) = k5_relat_1(k4_relat_1(B_38),A_10)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k4_relat_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_206])).

tff(c_1604,plain,(
    ! [A_74] :
      ( k5_relat_1(k4_relat_1('#skF_1'),A_74) = k4_relat_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_224])).

tff(c_1771,plain,(
    ! [A_77] :
      ( k5_relat_1('#skF_1',A_77) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_261,c_261,c_1604])).

tff(c_1814,plain,(
    ! [A_78] :
      ( k5_relat_1('#skF_1',A_78) = '#skF_1'
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_16,c_1771])).

tff(c_1841,plain,(
    k5_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_1814])).

tff(c_1854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1841])).

tff(c_1855,plain,(
    k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1879,plain,(
    k5_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_1855])).

tff(c_1859,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_34])).

tff(c_1925,plain,(
    ! [A_85] :
      ( k2_relat_1(k4_relat_1(A_85)) = k1_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2048,plain,(
    ! [A_97] :
      ( ~ v1_xboole_0(k1_relat_1(A_97))
      | ~ v1_relat_1(k4_relat_1(A_97))
      | v1_xboole_0(k4_relat_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1925,c_20])).

tff(c_1857,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_2060,plain,(
    ! [A_98] :
      ( k4_relat_1(A_98) = '#skF_1'
      | ~ v1_xboole_0(k1_relat_1(A_98))
      | ~ v1_relat_1(k4_relat_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_2048,c_1857])).

tff(c_2069,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1859,c_2060])).

tff(c_2073,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4,c_2069])).

tff(c_2074,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2073])).

tff(c_2077,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_2074])).

tff(c_2081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2077])).

tff(c_2082,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2073])).

tff(c_2090,plain,(
    ! [A_15] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2082,c_30])).

tff(c_2133,plain,(
    ! [A_101] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_101)) = k4_relat_1(k5_relat_1(A_101,'#skF_1'))
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2090])).

tff(c_1969,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_91,B_92)),k1_relat_1(A_91))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1977,plain,(
    ! [B_92] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_92)),'#skF_1')
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1859,c_1969])).

tff(c_2007,plain,(
    ! [B_95] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_95)),'#skF_1')
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1977])).

tff(c_1858,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_1940,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1945,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1858,c_1940])).

tff(c_2016,plain,(
    ! [B_95] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_95)) = '#skF_1'
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_2007,c_1945])).

tff(c_2358,plain,(
    ! [A_107] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_107,'#skF_1'))) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2133,c_2016])).

tff(c_3132,plain,(
    ! [A_123] :
      ( k2_relat_1(k5_relat_1(A_123,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_123,'#skF_1'))
      | ~ v1_relat_1(k4_relat_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_26])).

tff(c_3149,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(A_7,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_3132])).

tff(c_3159,plain,(
    ! [A_124] :
      ( k2_relat_1(k5_relat_1(A_124,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3149])).

tff(c_3202,plain,(
    ! [A_125] :
      ( k2_relat_1(k5_relat_1(A_125,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_16,c_3159])).

tff(c_3214,plain,(
    ! [A_125] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1(A_125,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_125,'#skF_1'))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3202,c_20])).

tff(c_3230,plain,(
    ! [A_126] :
      ( ~ v1_relat_1(k5_relat_1(A_126,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_126,'#skF_1'))
      | ~ v1_relat_1(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3214])).

tff(c_3247,plain,(
    ! [A_127] :
      ( k5_relat_1(A_127,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_127,'#skF_1'))
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_3230,c_1857])).

tff(c_3264,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_3247])).

tff(c_3321,plain,(
    ! [A_130] :
      ( k5_relat_1(A_130,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3264])).

tff(c_3348,plain,(
    k5_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_3321])).

tff(c_3361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1879,c_3348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:10:02 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.87  
% 4.58/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.88  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.58/1.88  
% 4.58/1.88  %Foreground sorts:
% 4.58/1.88  
% 4.58/1.88  
% 4.58/1.88  %Background operators:
% 4.58/1.88  
% 4.58/1.88  
% 4.58/1.88  %Foreground operators:
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.58/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.58/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.58/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.58/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.58/1.88  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.58/1.88  
% 4.58/1.90  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.58/1.90  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.58/1.90  tff(f_95, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 4.58/1.90  tff(f_47, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.58/1.90  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.58/1.90  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.58/1.90  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.58/1.90  tff(f_61, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 4.58/1.90  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.58/1.90  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 4.58/1.90  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 4.58/1.90  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.58/1.90  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.58/1.90  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.58/1.90  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.90  tff(c_55, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.58/1.90  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_55])).
% 4.58/1.90  tff(c_36, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.58/1.90  tff(c_60, plain, (k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 4.58/1.90  tff(c_78, plain, (k5_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_60])).
% 4.58/1.90  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.58/1.90  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.90  tff(c_50, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.90  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_50])).
% 4.58/1.90  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.58/1.90  tff(c_63, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_34])).
% 4.58/1.90  tff(c_112, plain, (![A_27]: (k2_relat_1(k4_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.58/1.90  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.90  tff(c_227, plain, (![A_40]: (~v1_xboole_0(k1_relat_1(A_40)) | ~v1_relat_1(k4_relat_1(A_40)) | v1_xboole_0(k4_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_112, c_20])).
% 4.58/1.90  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.58/1.90  tff(c_61, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 4.58/1.90  tff(c_239, plain, (![A_41]: (k4_relat_1(A_41)='#skF_1' | ~v1_xboole_0(k1_relat_1(A_41)) | ~v1_relat_1(k4_relat_1(A_41)) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_227, c_61])).
% 4.58/1.90  tff(c_248, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_63, c_239])).
% 4.58/1.90  tff(c_252, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4, c_248])).
% 4.58/1.90  tff(c_253, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_252])).
% 4.58/1.90  tff(c_256, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_253])).
% 4.58/1.90  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_256])).
% 4.58/1.90  tff(c_261, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_252])).
% 4.58/1.90  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.58/1.90  tff(c_26, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.58/1.90  tff(c_30, plain, (![B_17, A_15]: (k5_relat_1(k4_relat_1(B_17), k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.90  tff(c_269, plain, (![A_15]: (k5_relat_1('#skF_1', k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_261, c_30])).
% 4.58/1.90  tff(c_488, plain, (![A_47]: (k5_relat_1('#skF_1', k4_relat_1(A_47))=k4_relat_1(k5_relat_1(A_47, '#skF_1')) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_269])).
% 4.58/1.90  tff(c_163, plain, (![A_34, B_35]: (r1_tarski(k1_relat_1(k5_relat_1(A_34, B_35)), k1_relat_1(A_34)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.58/1.90  tff(c_171, plain, (![B_35]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_35)), '#skF_1') | ~v1_relat_1(B_35) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_163])).
% 4.58/1.90  tff(c_175, plain, (![B_36]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_36)), '#skF_1') | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_171])).
% 4.58/1.90  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.90  tff(c_62, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 4.58/1.90  tff(c_140, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.90  tff(c_145, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_140])).
% 4.58/1.90  tff(c_181, plain, (![B_36]: (k1_relat_1(k5_relat_1('#skF_1', B_36))='#skF_1' | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_175, c_145])).
% 4.58/1.90  tff(c_544, plain, (![A_50]: (k1_relat_1(k4_relat_1(k5_relat_1(A_50, '#skF_1')))='#skF_1' | ~v1_relat_1(k4_relat_1(A_50)) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_488, c_181])).
% 4.58/1.90  tff(c_1299, plain, (![A_66]: (k2_relat_1(k5_relat_1(A_66, '#skF_1'))='#skF_1' | ~v1_relat_1(k4_relat_1(A_66)) | ~v1_relat_1(A_66) | ~v1_relat_1(k5_relat_1(A_66, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_544])).
% 4.58/1.90  tff(c_1316, plain, (![A_7]: (k2_relat_1(k5_relat_1(A_7, '#skF_1'))='#skF_1' | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_1299])).
% 4.58/1.90  tff(c_1326, plain, (![A_67]: (k2_relat_1(k5_relat_1(A_67, '#skF_1'))='#skF_1' | ~v1_relat_1(k4_relat_1(A_67)) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1316])).
% 4.58/1.90  tff(c_1411, plain, (![A_70]: (k2_relat_1(k5_relat_1(A_70, '#skF_1'))='#skF_1' | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_16, c_1326])).
% 4.58/1.90  tff(c_1423, plain, (![A_70]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1(A_70, '#skF_1')) | v1_xboole_0(k5_relat_1(A_70, '#skF_1')) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_1411, c_20])).
% 4.58/1.90  tff(c_1439, plain, (![A_71]: (~v1_relat_1(k5_relat_1(A_71, '#skF_1')) | v1_xboole_0(k5_relat_1(A_71, '#skF_1')) | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1423])).
% 4.58/1.90  tff(c_1456, plain, (![A_72]: (k5_relat_1(A_72, '#skF_1')='#skF_1' | ~v1_relat_1(k5_relat_1(A_72, '#skF_1')) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_1439, c_61])).
% 4.58/1.90  tff(c_1473, plain, (![A_7]: (k5_relat_1(A_7, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_1456])).
% 4.58/1.90  tff(c_1483, plain, (![A_73]: (k5_relat_1(A_73, '#skF_1')='#skF_1' | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1473])).
% 4.58/1.90  tff(c_1580, plain, (![A_74]: (k5_relat_1(k4_relat_1(A_74), '#skF_1')='#skF_1' | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_16, c_1483])).
% 4.58/1.90  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.58/1.90  tff(c_206, plain, (![B_38, A_39]: (k5_relat_1(k4_relat_1(B_38), k4_relat_1(A_39))=k4_relat_1(k5_relat_1(A_39, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.90  tff(c_224, plain, (![A_10, B_38]: (k4_relat_1(k5_relat_1(k4_relat_1(A_10), B_38))=k5_relat_1(k4_relat_1(B_38), A_10) | ~v1_relat_1(B_38) | ~v1_relat_1(k4_relat_1(A_10)) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_206])).
% 4.58/1.90  tff(c_1604, plain, (![A_74]: (k5_relat_1(k4_relat_1('#skF_1'), A_74)=k4_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_1580, c_224])).
% 4.58/1.90  tff(c_1771, plain, (![A_77]: (k5_relat_1('#skF_1', A_77)='#skF_1' | ~v1_relat_1(k4_relat_1(A_77)) | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_261, c_261, c_1604])).
% 4.58/1.90  tff(c_1814, plain, (![A_78]: (k5_relat_1('#skF_1', A_78)='#skF_1' | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_16, c_1771])).
% 4.58/1.90  tff(c_1841, plain, (k5_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_1814])).
% 4.58/1.90  tff(c_1854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1841])).
% 4.58/1.90  tff(c_1855, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.58/1.90  tff(c_1879, plain, (k5_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_1855])).
% 4.58/1.90  tff(c_1859, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_34])).
% 4.58/1.90  tff(c_1925, plain, (![A_85]: (k2_relat_1(k4_relat_1(A_85))=k1_relat_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.58/1.90  tff(c_2048, plain, (![A_97]: (~v1_xboole_0(k1_relat_1(A_97)) | ~v1_relat_1(k4_relat_1(A_97)) | v1_xboole_0(k4_relat_1(A_97)) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_1925, c_20])).
% 4.58/1.90  tff(c_1857, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 4.58/1.90  tff(c_2060, plain, (![A_98]: (k4_relat_1(A_98)='#skF_1' | ~v1_xboole_0(k1_relat_1(A_98)) | ~v1_relat_1(k4_relat_1(A_98)) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_2048, c_1857])).
% 4.58/1.90  tff(c_2069, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1859, c_2060])).
% 4.58/1.90  tff(c_2073, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4, c_2069])).
% 4.58/1.90  tff(c_2074, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2073])).
% 4.58/1.90  tff(c_2077, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_2074])).
% 4.58/1.90  tff(c_2081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2077])).
% 4.58/1.90  tff(c_2082, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2073])).
% 4.58/1.90  tff(c_2090, plain, (![A_15]: (k5_relat_1('#skF_1', k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_2082, c_30])).
% 4.58/1.90  tff(c_2133, plain, (![A_101]: (k5_relat_1('#skF_1', k4_relat_1(A_101))=k4_relat_1(k5_relat_1(A_101, '#skF_1')) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2090])).
% 4.58/1.90  tff(c_1969, plain, (![A_91, B_92]: (r1_tarski(k1_relat_1(k5_relat_1(A_91, B_92)), k1_relat_1(A_91)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.58/1.90  tff(c_1977, plain, (![B_92]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_92)), '#skF_1') | ~v1_relat_1(B_92) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1859, c_1969])).
% 4.58/1.90  tff(c_2007, plain, (![B_95]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_95)), '#skF_1') | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1977])).
% 4.58/1.90  tff(c_1858, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 4.58/1.90  tff(c_1940, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.90  tff(c_1945, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_1858, c_1940])).
% 4.58/1.90  tff(c_2016, plain, (![B_95]: (k1_relat_1(k5_relat_1('#skF_1', B_95))='#skF_1' | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_2007, c_1945])).
% 4.58/1.90  tff(c_2358, plain, (![A_107]: (k1_relat_1(k4_relat_1(k5_relat_1(A_107, '#skF_1')))='#skF_1' | ~v1_relat_1(k4_relat_1(A_107)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_2133, c_2016])).
% 4.58/1.90  tff(c_3132, plain, (![A_123]: (k2_relat_1(k5_relat_1(A_123, '#skF_1'))='#skF_1' | ~v1_relat_1(k5_relat_1(A_123, '#skF_1')) | ~v1_relat_1(k4_relat_1(A_123)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_2358, c_26])).
% 4.58/1.90  tff(c_3149, plain, (![A_7]: (k2_relat_1(k5_relat_1(A_7, '#skF_1'))='#skF_1' | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_3132])).
% 4.58/1.90  tff(c_3159, plain, (![A_124]: (k2_relat_1(k5_relat_1(A_124, '#skF_1'))='#skF_1' | ~v1_relat_1(k4_relat_1(A_124)) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3149])).
% 4.58/1.90  tff(c_3202, plain, (![A_125]: (k2_relat_1(k5_relat_1(A_125, '#skF_1'))='#skF_1' | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_16, c_3159])).
% 4.58/1.90  tff(c_3214, plain, (![A_125]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1(A_125, '#skF_1')) | v1_xboole_0(k5_relat_1(A_125, '#skF_1')) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_3202, c_20])).
% 4.58/1.90  tff(c_3230, plain, (![A_126]: (~v1_relat_1(k5_relat_1(A_126, '#skF_1')) | v1_xboole_0(k5_relat_1(A_126, '#skF_1')) | ~v1_relat_1(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3214])).
% 4.58/1.90  tff(c_3247, plain, (![A_127]: (k5_relat_1(A_127, '#skF_1')='#skF_1' | ~v1_relat_1(k5_relat_1(A_127, '#skF_1')) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_3230, c_1857])).
% 4.58/1.90  tff(c_3264, plain, (![A_7]: (k5_relat_1(A_7, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_3247])).
% 4.58/1.90  tff(c_3321, plain, (![A_130]: (k5_relat_1(A_130, '#skF_1')='#skF_1' | ~v1_relat_1(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3264])).
% 4.58/1.90  tff(c_3348, plain, (k5_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_3321])).
% 4.58/1.90  tff(c_3361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1879, c_3348])).
% 4.58/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.90  
% 4.58/1.90  Inference rules
% 4.58/1.90  ----------------------
% 4.58/1.90  #Ref     : 0
% 4.58/1.90  #Sup     : 839
% 4.58/1.90  #Fact    : 0
% 4.58/1.90  #Define  : 0
% 4.58/1.90  #Split   : 6
% 4.58/1.90  #Chain   : 0
% 4.58/1.90  #Close   : 0
% 4.58/1.90  
% 4.58/1.90  Ordering : KBO
% 4.58/1.90  
% 4.58/1.90  Simplification rules
% 4.58/1.90  ----------------------
% 4.58/1.90  #Subsume      : 100
% 4.58/1.90  #Demod        : 879
% 4.58/1.90  #Tautology    : 282
% 4.58/1.90  #SimpNegUnit  : 2
% 4.58/1.90  #BackRed      : 16
% 4.58/1.90  
% 4.58/1.90  #Partial instantiations: 0
% 4.58/1.90  #Strategies tried      : 1
% 4.58/1.90  
% 4.58/1.90  Timing (in seconds)
% 4.58/1.90  ----------------------
% 4.58/1.90  Preprocessing        : 0.32
% 4.58/1.90  Parsing              : 0.18
% 4.58/1.90  CNF conversion       : 0.02
% 4.58/1.90  Main loop            : 0.77
% 4.58/1.90  Inferencing          : 0.26
% 4.58/1.90  Reduction            : 0.23
% 4.58/1.90  Demodulation         : 0.17
% 4.58/1.90  BG Simplification    : 0.04
% 4.58/1.90  Subsumption          : 0.18
% 4.58/1.90  Abstraction          : 0.04
% 4.58/1.90  MUC search           : 0.00
% 4.58/1.90  Cooper               : 0.00
% 4.58/1.90  Total                : 1.13
% 4.58/1.90  Index Insertion      : 0.00
% 4.58/1.90  Index Deletion       : 0.00
% 4.58/1.90  Index Matching       : 0.00
% 4.58/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
