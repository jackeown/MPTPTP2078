%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 458 expanded)
%              Number of leaves         :   31 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 918 expanded)
%              Number of equality atoms :   43 ( 260 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [A_48,B_49] :
      ( v1_xboole_0(A_48)
      | ~ v1_xboole_0(B_49)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_130])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_149,plain,(
    ! [A_50,B_51] :
      ( k6_setfam_1(A_50,B_51) = k1_setfam_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_165,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_149])).

tff(c_311,plain,(
    ! [A_75,B_76] :
      ( k8_setfam_1(A_75,B_76) = k6_setfam_1(A_75,B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_326,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_311])).

tff(c_339,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_326])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_166,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_329,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_311])).

tff(c_341,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_329])).

tff(c_361,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_341])).

tff(c_362,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_53,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_33,B_34] : r1_xboole_0(k1_xboole_0,k2_xboole_0(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_83,plain,(
    ! [B_42,A_43] :
      ( ~ r1_xboole_0(B_42,A_43)
      | ~ r1_tarski(B_42,A_43)
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_33,B_34] :
      ( ~ r1_tarski(k1_xboole_0,k2_xboole_0(A_33,B_34))
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_86])).

tff(c_350,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_92])).

tff(c_363,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_350])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_363])).

tff(c_374,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_16,plain,(
    ! [A_14] :
      ( k8_setfam_1(A_14,k1_xboole_0) = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_14] : k8_setfam_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_354,plain,(
    ! [A_14] : k8_setfam_1(A_14,'#skF_2') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_40])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_415,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_32])).

tff(c_445,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_415])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k8_setfam_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_449,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_20])).

tff(c_453,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_449])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_464,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_453,c_24])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_464])).

tff(c_472,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_setfam_1(B_26),k1_setfam_1(A_25))
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_498,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_504,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_92])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_504])).

tff(c_513,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_471,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_473,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_32])).

tff(c_515,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_473])).

tff(c_527,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_515])).

tff(c_530,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_527])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_530])).

tff(c_534,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_561,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_534,c_2])).

tff(c_533,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_557,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_578,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_557])).

tff(c_567,plain,(
    ! [A_10] : m1_subset_1('#skF_2',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_12])).

tff(c_629,plain,(
    ! [A_10] : m1_subset_1('#skF_3',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_567])).

tff(c_566,plain,(
    ! [A_14] : k8_setfam_1(A_14,'#skF_2') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_40])).

tff(c_605,plain,(
    ! [A_14] : k8_setfam_1(A_14,'#skF_3') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_566])).

tff(c_699,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k8_setfam_1(A_104,B_105),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_714,plain,(
    ! [A_14] :
      ( m1_subset_1(A_14,k1_zfmisc_1(A_14))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_699])).

tff(c_721,plain,(
    ! [A_106] : m1_subset_1(A_106,k1_zfmisc_1(A_106)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_714])).

tff(c_737,plain,(
    ! [A_106] : r1_tarski(A_106,A_106) ),
    inference(resolution,[status(thm)],[c_721,c_24])).

tff(c_586,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_32])).

tff(c_691,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_605,c_586])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  
% 2.90/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.47  
% 2.90/1.47  %Foreground sorts:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Background operators:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Foreground operators:
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.47  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.90/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.47  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.90/1.47  
% 3.02/1.49  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.02/1.49  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.49  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.02/1.49  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.02/1.49  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.02/1.49  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.02/1.49  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.02/1.49  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.02/1.49  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.02/1.49  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.02/1.49  tff(f_87, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.02/1.49  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.02/1.49  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.49  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.49  tff(c_111, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.49  tff(c_130, plain, (![A_48, B_49]: (v1_xboole_0(A_48) | ~v1_xboole_0(B_49) | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_26, c_111])).
% 3.02/1.49  tff(c_147, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_130])).
% 3.02/1.49  tff(c_148, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_147])).
% 3.02/1.49  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.49  tff(c_149, plain, (![A_50, B_51]: (k6_setfam_1(A_50, B_51)=k1_setfam_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.02/1.49  tff(c_165, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_149])).
% 3.02/1.49  tff(c_311, plain, (![A_75, B_76]: (k8_setfam_1(A_75, B_76)=k6_setfam_1(A_75, B_76) | k1_xboole_0=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.02/1.49  tff(c_326, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_311])).
% 3.02/1.49  tff(c_339, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_326])).
% 3.02/1.49  tff(c_345, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_339])).
% 3.02/1.49  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.49  tff(c_166, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_149])).
% 3.02/1.49  tff(c_329, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_311])).
% 3.02/1.49  tff(c_341, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_329])).
% 3.02/1.49  tff(c_361, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_341])).
% 3.02/1.49  tff(c_362, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_361])).
% 3.02/1.49  tff(c_12, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.49  tff(c_65, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.49  tff(c_81, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_12, c_65])).
% 3.02/1.49  tff(c_53, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.49  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.49  tff(c_58, plain, (![A_33, B_34]: (r1_xboole_0(k1_xboole_0, k2_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_8])).
% 3.02/1.49  tff(c_83, plain, (![B_42, A_43]: (~r1_xboole_0(B_42, A_43) | ~r1_tarski(B_42, A_43) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.49  tff(c_86, plain, (![A_33, B_34]: (~r1_tarski(k1_xboole_0, k2_xboole_0(A_33, B_34)) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_83])).
% 3.02/1.49  tff(c_92, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_86])).
% 3.02/1.49  tff(c_350, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_92])).
% 3.02/1.49  tff(c_363, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_350])).
% 3.02/1.49  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_363])).
% 3.02/1.49  tff(c_374, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_361])).
% 3.02/1.49  tff(c_16, plain, (![A_14]: (k8_setfam_1(A_14, k1_xboole_0)=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.02/1.49  tff(c_40, plain, (![A_14]: (k8_setfam_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 3.02/1.49  tff(c_354, plain, (![A_14]: (k8_setfam_1(A_14, '#skF_2')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_40])).
% 3.02/1.49  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.49  tff(c_415, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_32])).
% 3.02/1.49  tff(c_445, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_415])).
% 3.02/1.49  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k8_setfam_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.49  tff(c_449, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_374, c_20])).
% 3.02/1.49  tff(c_453, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_449])).
% 3.02/1.49  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.49  tff(c_464, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_453, c_24])).
% 3.02/1.49  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_464])).
% 3.02/1.49  tff(c_472, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_339])).
% 3.02/1.49  tff(c_30, plain, (![B_26, A_25]: (r1_tarski(k1_setfam_1(B_26), k1_setfam_1(A_25)) | k1_xboole_0=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.02/1.49  tff(c_498, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_341])).
% 3.02/1.49  tff(c_504, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_92])).
% 3.02/1.49  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_504])).
% 3.02/1.49  tff(c_513, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_341])).
% 3.02/1.49  tff(c_471, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_339])).
% 3.02/1.49  tff(c_473, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_32])).
% 3.02/1.49  tff(c_515, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_473])).
% 3.02/1.49  tff(c_527, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_515])).
% 3.02/1.49  tff(c_530, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_527])).
% 3.02/1.49  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_530])).
% 3.02/1.49  tff(c_534, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_147])).
% 3.02/1.49  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.49  tff(c_561, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_534, c_2])).
% 3.02/1.49  tff(c_533, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_147])).
% 3.02/1.49  tff(c_557, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_533, c_2])).
% 3.02/1.49  tff(c_578, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_561, c_557])).
% 3.02/1.49  tff(c_567, plain, (![A_10]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_12])).
% 3.02/1.49  tff(c_629, plain, (![A_10]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_567])).
% 3.02/1.49  tff(c_566, plain, (![A_14]: (k8_setfam_1(A_14, '#skF_2')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_557, c_40])).
% 3.02/1.49  tff(c_605, plain, (![A_14]: (k8_setfam_1(A_14, '#skF_3')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_578, c_566])).
% 3.02/1.49  tff(c_699, plain, (![A_104, B_105]: (m1_subset_1(k8_setfam_1(A_104, B_105), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.49  tff(c_714, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(superposition, [status(thm), theory('equality')], [c_605, c_699])).
% 3.02/1.49  tff(c_721, plain, (![A_106]: (m1_subset_1(A_106, k1_zfmisc_1(A_106)))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_714])).
% 3.02/1.49  tff(c_737, plain, (![A_106]: (r1_tarski(A_106, A_106))), inference(resolution, [status(thm)], [c_721, c_24])).
% 3.02/1.49  tff(c_586, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_32])).
% 3.02/1.49  tff(c_691, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_605, c_586])).
% 3.02/1.49  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_737, c_691])).
% 3.02/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  Inference rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Ref     : 0
% 3.02/1.49  #Sup     : 141
% 3.02/1.49  #Fact    : 0
% 3.02/1.49  #Define  : 0
% 3.02/1.49  #Split   : 6
% 3.02/1.49  #Chain   : 0
% 3.02/1.49  #Close   : 0
% 3.02/1.49  
% 3.02/1.49  Ordering : KBO
% 3.02/1.49  
% 3.02/1.49  Simplification rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Subsume      : 8
% 3.02/1.49  #Demod        : 118
% 3.02/1.49  #Tautology    : 81
% 3.02/1.49  #SimpNegUnit  : 4
% 3.02/1.49  #BackRed      : 51
% 3.02/1.49  
% 3.02/1.49  #Partial instantiations: 0
% 3.02/1.49  #Strategies tried      : 1
% 3.02/1.49  
% 3.02/1.49  Timing (in seconds)
% 3.02/1.49  ----------------------
% 3.02/1.50  Preprocessing        : 0.30
% 3.02/1.50  Parsing              : 0.16
% 3.02/1.50  CNF conversion       : 0.02
% 3.02/1.50  Main loop            : 0.34
% 3.02/1.50  Inferencing          : 0.13
% 3.02/1.50  Reduction            : 0.11
% 3.02/1.50  Demodulation         : 0.08
% 3.02/1.50  BG Simplification    : 0.02
% 3.02/1.50  Subsumption          : 0.05
% 3.02/1.50  Abstraction          : 0.02
% 3.02/1.50  MUC search           : 0.00
% 3.02/1.50  Cooper               : 0.00
% 3.02/1.50  Total                : 0.68
% 3.02/1.50  Index Insertion      : 0.00
% 3.02/1.50  Index Deletion       : 0.00
% 3.02/1.50  Index Matching       : 0.00
% 3.02/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
