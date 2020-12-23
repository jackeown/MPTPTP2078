%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 244 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 446 expanded)
%              Number of equality atoms :   36 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_96,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1199,plain,(
    ! [B_104,A_105] :
      ( r1_xboole_0(k1_relat_1(B_104),A_105)
      | k7_relat_1(B_104,A_105) != k1_xboole_0
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_74,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_147,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_842,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_848,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_842])).

tff(c_859,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_848])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_866,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_32])).

tff(c_876,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_866])).

tff(c_878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_876])).

tff(c_880,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1205,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1199,c_880])).

tff(c_1212,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1205])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_918,plain,(
    ! [A_78] :
      ( k7_relat_1(A_78,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_929,plain,(
    ! [A_5] : k7_relat_1(k6_relat_1(A_5),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_918])).

tff(c_1013,plain,(
    ! [A_87,B_88] :
      ( v1_xboole_0(k7_relat_1(A_87,B_88))
      | ~ v1_relat_1(A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1019,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_xboole_0(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_1013])).

tff(c_1028,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k6_relat_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1019])).

tff(c_1068,plain,(
    ! [A_92] : ~ v1_xboole_0(k6_relat_1(A_92)) ),
    inference(splitLeft,[status(thm)],[c_1028])).

tff(c_1070,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1068])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_887,plain,(
    ! [A_76] :
      ( k8_relat_1(k1_xboole_0,A_76) = k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_897,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_887])).

tff(c_973,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k8_relat_1(A_82,B_83),B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_979,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_973])).

tff(c_986,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_979])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1071,plain,(
    ! [B_93,A_94] :
      ( ~ r1_xboole_0(B_93,A_94)
      | ~ r1_tarski(B_93,A_94)
      | v1_xboole_0(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1076,plain,(
    ! [A_95] :
      ( ~ r1_tarski(A_95,k1_xboole_0)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_1071])).

tff(c_1082,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_986,c_1076])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_1082])).

tff(c_1092,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_879,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1103,plain,(
    ! [B_98,A_99] :
      ( k2_relat_1(k7_relat_1(B_98,A_99)) = k9_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2296,plain,(
    ! [B_153,A_154] :
      ( ~ v1_xboole_0(k9_relat_1(B_153,A_154))
      | ~ v1_relat_1(k7_relat_1(B_153,A_154))
      | v1_xboole_0(k7_relat_1(B_153,A_154))
      | ~ v1_relat_1(B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_18])).

tff(c_2323,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_2296])).

tff(c_2340,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1092,c_2323])).

tff(c_2341,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2340])).

tff(c_2344,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_2341])).

tff(c_2348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2344])).

tff(c_2350,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2340])).

tff(c_26,plain,(
    ! [A_16] :
      ( k8_relat_1(k1_xboole_0,A_16) = k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2362,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2350,c_26])).

tff(c_30,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2476,plain,(
    ! [B_155,A_156,A_157] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_155,A_156),A_157),k9_relat_1(B_155,A_156))
      | ~ v1_relat_1(k7_relat_1(B_155,A_156))
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_28])).

tff(c_2534,plain,(
    ! [A_157] :
      ( r1_tarski(k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_157),k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_2476])).

tff(c_2620,plain,(
    ! [A_158] : r1_tarski(k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_158),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2350,c_2534])).

tff(c_2633,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2620])).

tff(c_2639,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2350,c_2633])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k8_relat_1(A_14,B_15) = B_15
      | ~ r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2696,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2639,c_24])).

tff(c_2705,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2350,c_2362,c_2696])).

tff(c_2707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1212,c_2705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.67  
% 3.79/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.67  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 3.79/1.67  
% 3.79/1.67  %Foreground sorts:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Background operators:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Foreground operators:
% 3.79/1.67  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.79/1.67  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.79/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.79/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.79/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.79/1.67  
% 3.93/1.69  tff(f_109, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.93/1.69  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.93/1.69  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.93/1.69  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.93/1.69  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.93/1.69  tff(f_96, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.93/1.69  tff(f_42, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.93/1.69  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 3.93/1.69  tff(f_54, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 3.93/1.69  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 3.93/1.69  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 3.93/1.69  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.93/1.69  tff(f_36, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.93/1.69  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.93/1.69  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.93/1.69  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.93/1.69  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.93/1.69  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.93/1.69  tff(c_1199, plain, (![B_104, A_105]: (r1_xboole_0(k1_relat_1(B_104), A_105) | k7_relat_1(B_104, A_105)!=k1_xboole_0 | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.93/1.69  tff(c_52, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.93/1.69  tff(c_74, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 3.93/1.69  tff(c_46, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.93/1.69  tff(c_147, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46])).
% 3.93/1.69  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.93/1.69  tff(c_842, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.93/1.69  tff(c_848, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_842])).
% 3.93/1.69  tff(c_859, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_848])).
% 3.93/1.69  tff(c_32, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.93/1.69  tff(c_866, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_859, c_32])).
% 3.93/1.69  tff(c_876, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_866])).
% 3.93/1.69  tff(c_878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_876])).
% 3.93/1.69  tff(c_880, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 3.93/1.69  tff(c_1205, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1199, c_880])).
% 3.93/1.69  tff(c_1212, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1205])).
% 3.93/1.69  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.93/1.69  tff(c_38, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.93/1.69  tff(c_10, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.93/1.69  tff(c_918, plain, (![A_78]: (k7_relat_1(A_78, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.93/1.69  tff(c_929, plain, (![A_5]: (k7_relat_1(k6_relat_1(A_5), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_918])).
% 3.93/1.69  tff(c_1013, plain, (![A_87, B_88]: (v1_xboole_0(k7_relat_1(A_87, B_88)) | ~v1_relat_1(A_87) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.93/1.69  tff(c_1019, plain, (![A_5]: (v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_xboole_0(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_929, c_1013])).
% 3.93/1.69  tff(c_1028, plain, (![A_5]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k6_relat_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1019])).
% 3.93/1.69  tff(c_1068, plain, (![A_92]: (~v1_xboole_0(k6_relat_1(A_92)))), inference(splitLeft, [status(thm)], [c_1028])).
% 3.93/1.69  tff(c_1070, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_1068])).
% 3.93/1.69  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 3.93/1.69  tff(c_887, plain, (![A_76]: (k8_relat_1(k1_xboole_0, A_76)=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.69  tff(c_897, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_887])).
% 3.93/1.69  tff(c_973, plain, (![A_82, B_83]: (r1_tarski(k8_relat_1(A_82, B_83), B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.69  tff(c_979, plain, (r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_897, c_973])).
% 3.93/1.69  tff(c_986, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_979])).
% 3.93/1.69  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.93/1.69  tff(c_1071, plain, (![B_93, A_94]: (~r1_xboole_0(B_93, A_94) | ~r1_tarski(B_93, A_94) | v1_xboole_0(B_93))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.93/1.69  tff(c_1076, plain, (![A_95]: (~r1_tarski(A_95, k1_xboole_0) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_4, c_1071])).
% 3.93/1.69  tff(c_1082, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_986, c_1076])).
% 3.93/1.69  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1070, c_1082])).
% 3.93/1.69  tff(c_1092, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1028])).
% 3.93/1.69  tff(c_879, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.93/1.69  tff(c_1103, plain, (![B_98, A_99]: (k2_relat_1(k7_relat_1(B_98, A_99))=k9_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.93/1.69  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.93/1.69  tff(c_2296, plain, (![B_153, A_154]: (~v1_xboole_0(k9_relat_1(B_153, A_154)) | ~v1_relat_1(k7_relat_1(B_153, A_154)) | v1_xboole_0(k7_relat_1(B_153, A_154)) | ~v1_relat_1(B_153))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_18])).
% 3.93/1.69  tff(c_2323, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_879, c_2296])).
% 3.93/1.69  tff(c_2340, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1092, c_2323])).
% 3.93/1.69  tff(c_2341, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2340])).
% 3.93/1.69  tff(c_2344, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_2341])).
% 3.93/1.69  tff(c_2348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2344])).
% 3.93/1.69  tff(c_2350, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_2340])).
% 3.93/1.69  tff(c_26, plain, (![A_16]: (k8_relat_1(k1_xboole_0, A_16)=k1_xboole_0 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.69  tff(c_2362, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2350, c_26])).
% 3.93/1.69  tff(c_30, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.93/1.69  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.93/1.69  tff(c_2476, plain, (![B_155, A_156, A_157]: (r1_tarski(k9_relat_1(k7_relat_1(B_155, A_156), A_157), k9_relat_1(B_155, A_156)) | ~v1_relat_1(k7_relat_1(B_155, A_156)) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_28])).
% 3.93/1.69  tff(c_2534, plain, (![A_157]: (r1_tarski(k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_157), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_879, c_2476])).
% 3.93/1.69  tff(c_2620, plain, (![A_158]: (r1_tarski(k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_158), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2350, c_2534])).
% 3.93/1.69  tff(c_2633, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2620])).
% 3.93/1.69  tff(c_2639, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2350, c_2633])).
% 3.93/1.69  tff(c_24, plain, (![A_14, B_15]: (k8_relat_1(A_14, B_15)=B_15 | ~r1_tarski(k2_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.93/1.69  tff(c_2696, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_2639, c_24])).
% 3.93/1.69  tff(c_2705, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2350, c_2362, c_2696])).
% 3.93/1.69  tff(c_2707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1212, c_2705])).
% 3.93/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.69  
% 3.93/1.69  Inference rules
% 3.93/1.69  ----------------------
% 3.93/1.69  #Ref     : 0
% 3.93/1.69  #Sup     : 657
% 3.93/1.69  #Fact    : 0
% 3.93/1.69  #Define  : 0
% 3.93/1.69  #Split   : 5
% 3.93/1.69  #Chain   : 0
% 3.93/1.69  #Close   : 0
% 3.93/1.69  
% 3.93/1.69  Ordering : KBO
% 3.93/1.69  
% 3.93/1.69  Simplification rules
% 3.93/1.69  ----------------------
% 3.93/1.69  #Subsume      : 9
% 3.93/1.69  #Demod        : 779
% 3.93/1.69  #Tautology    : 497
% 3.93/1.69  #SimpNegUnit  : 3
% 3.93/1.69  #BackRed      : 0
% 3.93/1.69  
% 3.93/1.69  #Partial instantiations: 0
% 3.93/1.69  #Strategies tried      : 1
% 3.93/1.69  
% 3.93/1.69  Timing (in seconds)
% 3.93/1.69  ----------------------
% 3.93/1.69  Preprocessing        : 0.31
% 3.93/1.69  Parsing              : 0.17
% 3.93/1.69  CNF conversion       : 0.02
% 3.93/1.69  Main loop            : 0.57
% 3.93/1.69  Inferencing          : 0.21
% 3.93/1.69  Reduction            : 0.21
% 3.93/1.69  Demodulation         : 0.15
% 3.93/1.69  BG Simplification    : 0.02
% 3.93/1.69  Subsumption          : 0.09
% 3.93/1.69  Abstraction          : 0.03
% 3.93/1.69  MUC search           : 0.00
% 3.93/1.69  Cooper               : 0.00
% 3.93/1.69  Total                : 0.91
% 3.93/1.69  Index Insertion      : 0.00
% 3.93/1.69  Index Deletion       : 0.00
% 3.93/1.69  Index Matching       : 0.00
% 3.93/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
