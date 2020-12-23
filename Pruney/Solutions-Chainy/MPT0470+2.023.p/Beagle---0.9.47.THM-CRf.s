%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 305 expanded)
%              Number of leaves         :   27 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 520 expanded)
%              Number of equality atoms :   54 ( 161 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

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

tff(c_324,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_relat_1(k4_relat_1(A_43))
      | v1_xboole_0(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
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

tff(c_429,plain,(
    ! [A_47] :
      ( k4_relat_1(A_47) = '#skF_1'
      | ~ v1_xboole_0(k1_relat_1(A_47))
      | ~ v1_relat_1(k4_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(resolution,[status(thm)],[c_324,c_61])).

tff(c_435,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_429])).

tff(c_437,plain,
    ( k4_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4,c_435])).

tff(c_466,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_469,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_466])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_469])).

tff(c_474,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_32])).

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

tff(c_185,plain,(
    ! [A_37] :
      ( k2_relat_1(k5_relat_1(A_37,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_175,c_145])).

tff(c_200,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1(A_37,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_37,'#skF_1'))
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_20])).

tff(c_232,plain,(
    ! [A_40] :
      ( ~ v1_relat_1(k5_relat_1(A_40,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_40,'#skF_1'))
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_241,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_41,'#skF_1'))
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_232,c_61])).

tff(c_245,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_241])).

tff(c_249,plain,(
    ! [A_42] :
      ( k5_relat_1(A_42,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_245])).

tff(c_263,plain,(
    ! [A_6] :
      ( k5_relat_1(k4_relat_1(A_6),'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_249])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_17,A_15] :
      ( k5_relat_1(k4_relat_1(B_17),k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_485,plain,(
    ! [A_15] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_30])).

tff(c_521,plain,(
    ! [A_50] :
      ( k5_relat_1('#skF_1',k4_relat_1(A_50)) = k4_relat_1(k5_relat_1(A_50,'#skF_1'))
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_485])).

tff(c_701,plain,(
    ! [A_55] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_55),'#skF_1')) = k5_relat_1('#skF_1',A_55)
      | ~ v1_relat_1(k4_relat_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_521])).

tff(c_761,plain,(
    ! [A_6] :
      ( k5_relat_1('#skF_1',A_6) = k4_relat_1('#skF_1')
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_701])).

tff(c_860,plain,(
    ! [A_59] :
      ( k5_relat_1('#skF_1',A_59) = '#skF_1'
      | ~ v1_relat_1(k4_relat_1(A_59))
      | ~ v1_relat_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_761])).

tff(c_893,plain,(
    ! [A_60] :
      ( k5_relat_1('#skF_1',A_60) = '#skF_1'
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_16,c_860])).

tff(c_914,plain,(
    k5_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_893])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_914])).

tff(c_926,plain,(
    k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_928,plain,(
    k5_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_926])).

tff(c_932,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_32])).

tff(c_1040,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_73,B_74)),k2_relat_1(B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1048,plain,(
    ! [A_73] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_73,'#skF_1')),'#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_1040])).

tff(c_1057,plain,(
    ! [A_75] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_75,'#skF_1')),'#skF_1')
      | ~ v1_relat_1(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1048])).

tff(c_930,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_1017,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1022,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_930,c_1017])).

tff(c_1067,plain,(
    ! [A_76] :
      ( k2_relat_1(k5_relat_1(A_76,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_1057,c_1022])).

tff(c_1082,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1(A_76,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_76,'#skF_1'))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_20])).

tff(c_1114,plain,(
    ! [A_79] :
      ( ~ v1_relat_1(k5_relat_1(A_79,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_79,'#skF_1'))
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1082])).

tff(c_929,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_1123,plain,(
    ! [A_80] :
      ( k5_relat_1(A_80,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_80,'#skF_1'))
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_1114,c_929])).

tff(c_1127,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_1123])).

tff(c_1143,plain,(
    ! [A_82] :
      ( k5_relat_1(A_82,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1127])).

tff(c_1155,plain,(
    k5_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_1143])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.83/1.42  
% 2.83/1.42  %Foreground sorts:
% 2.83/1.42  
% 2.83/1.42  
% 2.83/1.42  %Background operators:
% 2.83/1.42  
% 2.83/1.42  
% 2.83/1.42  %Foreground operators:
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.42  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.83/1.42  
% 2.83/1.44  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.83/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.83/1.44  tff(f_95, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.83/1.44  tff(f_47, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.83/1.44  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.83/1.44  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.83/1.44  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.83/1.44  tff(f_61, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.83/1.44  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.83/1.44  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.83/1.44  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.44  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.44  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.83/1.44  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.83/1.44  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.44  tff(c_55, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.44  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_55])).
% 2.83/1.44  tff(c_36, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.44  tff(c_60, plain, (k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.83/1.44  tff(c_78, plain, (k5_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_60])).
% 2.83/1.44  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.44  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.44  tff(c_50, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.44  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_50])).
% 2.83/1.44  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.44  tff(c_63, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_34])).
% 2.83/1.44  tff(c_112, plain, (![A_27]: (k2_relat_1(k4_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.83/1.44  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.44  tff(c_324, plain, (![A_43]: (~v1_xboole_0(k1_relat_1(A_43)) | ~v1_relat_1(k4_relat_1(A_43)) | v1_xboole_0(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_112, c_20])).
% 2.83/1.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.44  tff(c_61, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 2.83/1.44  tff(c_429, plain, (![A_47]: (k4_relat_1(A_47)='#skF_1' | ~v1_xboole_0(k1_relat_1(A_47)) | ~v1_relat_1(k4_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(resolution, [status(thm)], [c_324, c_61])).
% 2.83/1.44  tff(c_435, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_63, c_429])).
% 2.83/1.44  tff(c_437, plain, (k4_relat_1('#skF_1')='#skF_1' | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4, c_435])).
% 2.83/1.44  tff(c_466, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_437])).
% 2.83/1.44  tff(c_469, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_466])).
% 2.83/1.44  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_469])).
% 2.83/1.44  tff(c_474, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_437])).
% 2.83/1.44  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.44  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.44  tff(c_64, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_32])).
% 2.83/1.44  tff(c_163, plain, (![A_34, B_35]: (r1_tarski(k2_relat_1(k5_relat_1(A_34, B_35)), k2_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.44  tff(c_171, plain, (![A_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_34, '#skF_1')), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_64, c_163])).
% 2.83/1.44  tff(c_175, plain, (![A_36]: (r1_tarski(k2_relat_1(k5_relat_1(A_36, '#skF_1')), '#skF_1') | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_171])).
% 2.83/1.44  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.44  tff(c_62, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 2.83/1.44  tff(c_140, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.44  tff(c_145, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_140])).
% 2.83/1.44  tff(c_185, plain, (![A_37]: (k2_relat_1(k5_relat_1(A_37, '#skF_1'))='#skF_1' | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_175, c_145])).
% 2.83/1.44  tff(c_200, plain, (![A_37]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1(A_37, '#skF_1')) | v1_xboole_0(k5_relat_1(A_37, '#skF_1')) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_185, c_20])).
% 2.83/1.44  tff(c_232, plain, (![A_40]: (~v1_relat_1(k5_relat_1(A_40, '#skF_1')) | v1_xboole_0(k5_relat_1(A_40, '#skF_1')) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_200])).
% 2.83/1.44  tff(c_241, plain, (![A_41]: (k5_relat_1(A_41, '#skF_1')='#skF_1' | ~v1_relat_1(k5_relat_1(A_41, '#skF_1')) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_232, c_61])).
% 2.83/1.44  tff(c_245, plain, (![A_7]: (k5_relat_1(A_7, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_241])).
% 2.83/1.44  tff(c_249, plain, (![A_42]: (k5_relat_1(A_42, '#skF_1')='#skF_1' | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_245])).
% 2.83/1.44  tff(c_263, plain, (![A_6]: (k5_relat_1(k4_relat_1(A_6), '#skF_1')='#skF_1' | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_249])).
% 2.83/1.44  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.44  tff(c_30, plain, (![B_17, A_15]: (k5_relat_1(k4_relat_1(B_17), k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.44  tff(c_485, plain, (![A_15]: (k5_relat_1('#skF_1', k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_474, c_30])).
% 2.83/1.44  tff(c_521, plain, (![A_50]: (k5_relat_1('#skF_1', k4_relat_1(A_50))=k4_relat_1(k5_relat_1(A_50, '#skF_1')) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_485])).
% 2.83/1.44  tff(c_701, plain, (![A_55]: (k4_relat_1(k5_relat_1(k4_relat_1(A_55), '#skF_1'))=k5_relat_1('#skF_1', A_55) | ~v1_relat_1(k4_relat_1(A_55)) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_22, c_521])).
% 2.83/1.44  tff(c_761, plain, (![A_6]: (k5_relat_1('#skF_1', A_6)=k4_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_263, c_701])).
% 2.83/1.44  tff(c_860, plain, (![A_59]: (k5_relat_1('#skF_1', A_59)='#skF_1' | ~v1_relat_1(k4_relat_1(A_59)) | ~v1_relat_1(A_59) | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_761])).
% 2.83/1.44  tff(c_893, plain, (![A_60]: (k5_relat_1('#skF_1', A_60)='#skF_1' | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_16, c_860])).
% 2.83/1.44  tff(c_914, plain, (k5_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_893])).
% 2.83/1.44  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_914])).
% 2.83/1.44  tff(c_926, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.83/1.44  tff(c_928, plain, (k5_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_926])).
% 2.83/1.44  tff(c_932, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_32])).
% 2.83/1.44  tff(c_1040, plain, (![A_73, B_74]: (r1_tarski(k2_relat_1(k5_relat_1(A_73, B_74)), k2_relat_1(B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.44  tff(c_1048, plain, (![A_73]: (r1_tarski(k2_relat_1(k5_relat_1(A_73, '#skF_1')), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_932, c_1040])).
% 2.83/1.44  tff(c_1057, plain, (![A_75]: (r1_tarski(k2_relat_1(k5_relat_1(A_75, '#skF_1')), '#skF_1') | ~v1_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1048])).
% 2.83/1.44  tff(c_930, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 2.83/1.44  tff(c_1017, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.44  tff(c_1022, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_930, c_1017])).
% 2.83/1.44  tff(c_1067, plain, (![A_76]: (k2_relat_1(k5_relat_1(A_76, '#skF_1'))='#skF_1' | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_1057, c_1022])).
% 2.83/1.44  tff(c_1082, plain, (![A_76]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1(A_76, '#skF_1')) | v1_xboole_0(k5_relat_1(A_76, '#skF_1')) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_20])).
% 2.83/1.44  tff(c_1114, plain, (![A_79]: (~v1_relat_1(k5_relat_1(A_79, '#skF_1')) | v1_xboole_0(k5_relat_1(A_79, '#skF_1')) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1082])).
% 2.83/1.44  tff(c_929, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2])).
% 2.83/1.44  tff(c_1123, plain, (![A_80]: (k5_relat_1(A_80, '#skF_1')='#skF_1' | ~v1_relat_1(k5_relat_1(A_80, '#skF_1')) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_1114, c_929])).
% 2.83/1.44  tff(c_1127, plain, (![A_7]: (k5_relat_1(A_7, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_1123])).
% 2.83/1.44  tff(c_1143, plain, (![A_82]: (k5_relat_1(A_82, '#skF_1')='#skF_1' | ~v1_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1127])).
% 2.83/1.44  tff(c_1155, plain, (k5_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_1143])).
% 2.83/1.44  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_928, c_1155])).
% 2.83/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  Inference rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Ref     : 0
% 2.83/1.44  #Sup     : 267
% 2.83/1.44  #Fact    : 0
% 2.83/1.44  #Define  : 0
% 2.83/1.44  #Split   : 2
% 2.83/1.44  #Chain   : 0
% 2.83/1.44  #Close   : 0
% 2.83/1.44  
% 2.83/1.44  Ordering : KBO
% 2.83/1.44  
% 2.83/1.44  Simplification rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Subsume      : 17
% 2.83/1.44  #Demod        : 231
% 2.83/1.44  #Tautology    : 138
% 2.83/1.44  #SimpNegUnit  : 2
% 2.83/1.44  #BackRed      : 9
% 2.83/1.44  
% 2.83/1.44  #Partial instantiations: 0
% 2.83/1.44  #Strategies tried      : 1
% 2.83/1.44  
% 2.83/1.44  Timing (in seconds)
% 2.83/1.44  ----------------------
% 2.83/1.44  Preprocessing        : 0.29
% 2.83/1.44  Parsing              : 0.16
% 2.83/1.44  CNF conversion       : 0.02
% 2.83/1.44  Main loop            : 0.38
% 2.83/1.44  Inferencing          : 0.15
% 2.83/1.44  Reduction            : 0.11
% 2.83/1.44  Demodulation         : 0.08
% 2.83/1.44  BG Simplification    : 0.02
% 2.83/1.44  Subsumption          : 0.08
% 2.83/1.44  Abstraction          : 0.02
% 2.83/1.44  MUC search           : 0.00
% 2.83/1.44  Cooper               : 0.00
% 2.83/1.44  Total                : 0.71
% 2.83/1.44  Index Insertion      : 0.00
% 2.83/1.44  Index Deletion       : 0.00
% 2.83/1.44  Index Matching       : 0.00
% 2.83/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
