%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 366 expanded)
%              Number of leaves         :   32 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 704 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_545,plain,(
    ! [A_73,B_74] :
      ( k6_setfam_1(A_73,B_74) = k1_setfam_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_558,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_545])).

tff(c_589,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k6_setfam_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_599,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_589])).

tff(c_606,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_599])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_612,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_606,c_34])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_96,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    k4_xboole_0('#skF_2',k1_zfmisc_1('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_14])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_166,plain,(
    ! [B_49,A_50] :
      ( ~ r1_xboole_0(B_49,A_50)
      | ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_264,plain,(
    ! [A_59,B_60] :
      ( ~ r1_tarski(A_59,B_60)
      | v1_xboole_0(A_59)
      | k4_xboole_0(A_59,B_60) != A_59 ) ),
    inference(resolution,[status(thm)],[c_22,c_166])).

tff(c_273,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2',k1_zfmisc_1('#skF_1')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_264])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_273])).

tff(c_294,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_setfam_1(B_25),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_125])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ v1_xboole_0(k2_xboole_0(A_3,B_4))
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8])).

tff(c_165,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_108,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_96])).

tff(c_116,plain,(
    k4_xboole_0('#skF_3',k1_zfmisc_1('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_270,plain,
    ( v1_xboole_0('#skF_3')
    | k4_xboole_0('#skF_3',k1_zfmisc_1('#skF_1')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_108,c_264])).

tff(c_285,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_270])).

tff(c_286,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_285])).

tff(c_324,plain,(
    ! [A_64,B_65] :
      ( k6_setfam_1(A_64,B_65) = k1_setfam_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_324])).

tff(c_449,plain,(
    ! [A_70,B_71] :
      ( k8_setfam_1(A_70,B_71) = k6_setfam_1(A_70,B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_463,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_449])).

tff(c_470,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_463])).

tff(c_471,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_470])).

tff(c_336,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_324])).

tff(c_460,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_449])).

tff(c_467,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_460])).

tff(c_468,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_467])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_473,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_40])).

tff(c_490,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_473])).

tff(c_493,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_490])).

tff(c_499,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_493])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_499])).

tff(c_503,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_708,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = '#skF_2'
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_14])).

tff(c_728,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),'#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_612,c_708])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,(
    ! [A_53] :
      ( k8_setfam_1(A_53,k1_xboole_0) = A_53
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_215,plain,(
    ! [A_53] :
      ( k8_setfam_1(A_53,k1_xboole_0) = A_53
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_886,plain,(
    ! [A_94] :
      ( k8_setfam_1(A_94,'#skF_2') = A_94
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_503,c_215])).

tff(c_894,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_107,c_886])).

tff(c_508,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_286])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k8_setfam_1(A_16,B_17) = k6_setfam_1(A_16,B_17)
      | k1_xboole_0 = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_651,plain,(
    ! [A_79,B_80] :
      ( k8_setfam_1(A_79,B_80) = k6_setfam_1(A_79,B_80)
      | B_80 = '#skF_2'
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_28])).

tff(c_665,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_651])).

tff(c_672,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_665])).

tff(c_673,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_672])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_40])).

tff(c_517,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_80])).

tff(c_674,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_517])).

tff(c_895,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),'#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_674])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_895])).

tff(c_901,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_909,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_901,c_18])).

tff(c_900,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_905,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_900,c_18])).

tff(c_927,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_905])).

tff(c_935,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_40])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/2.03  
% 3.75/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/2.03  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.75/2.03  
% 3.75/2.03  %Foreground sorts:
% 3.75/2.03  
% 3.75/2.03  
% 3.75/2.03  %Background operators:
% 3.75/2.03  
% 3.75/2.03  
% 3.75/2.03  %Foreground operators:
% 3.75/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/2.03  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.75/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/2.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.75/2.03  tff('#skF_2', type, '#skF_2': $i).
% 3.75/2.03  tff('#skF_3', type, '#skF_3': $i).
% 3.75/2.03  tff('#skF_1', type, '#skF_1': $i).
% 3.75/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/2.03  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.75/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/2.03  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.75/2.03  
% 4.07/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.07/2.06  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 4.07/2.06  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 4.07/2.06  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 4.07/2.06  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.07/2.06  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.07/2.06  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.07/2.06  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.07/2.06  tff(f_92, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 4.07/2.06  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.07/2.06  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_xboole_0)).
% 4.07/2.06  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 4.07/2.06  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 4.07/2.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/2.06  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.07/2.06  tff(c_545, plain, (![A_73, B_74]: (k6_setfam_1(A_73, B_74)=k1_setfam_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.07/2.06  tff(c_558, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_545])).
% 4.07/2.06  tff(c_589, plain, (![A_77, B_78]: (m1_subset_1(k6_setfam_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.07/2.06  tff(c_599, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_558, c_589])).
% 4.07/2.06  tff(c_606, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_599])).
% 4.07/2.06  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.07/2.06  tff(c_612, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_606, c_34])).
% 4.07/2.06  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.07/2.06  tff(c_96, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.07/2.06  tff(c_107, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_96])).
% 4.07/2.06  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.07/2.06  tff(c_112, plain, (k4_xboole_0('#skF_2', k1_zfmisc_1('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_14])).
% 4.07/2.06  tff(c_22, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.07/2.06  tff(c_166, plain, (![B_49, A_50]: (~r1_xboole_0(B_49, A_50) | ~r1_tarski(B_49, A_50) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.07/2.06  tff(c_264, plain, (![A_59, B_60]: (~r1_tarski(A_59, B_60) | v1_xboole_0(A_59) | k4_xboole_0(A_59, B_60)!=A_59)), inference(resolution, [status(thm)], [c_22, c_166])).
% 4.07/2.06  tff(c_273, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', k1_zfmisc_1('#skF_1'))!='#skF_2'), inference(resolution, [status(thm)], [c_107, c_264])).
% 4.07/2.06  tff(c_288, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_273])).
% 4.07/2.06  tff(c_294, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_288])).
% 4.07/2.06  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.07/2.06  tff(c_38, plain, (![B_25, A_24]: (r1_tarski(k1_setfam_1(B_25), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/2.06  tff(c_125, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.07/2.06  tff(c_145, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_125])).
% 4.07/2.06  tff(c_8, plain, (![A_3, B_4]: (~v1_xboole_0(k2_xboole_0(A_3, B_4)) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/2.06  tff(c_161, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_8])).
% 4.07/2.06  tff(c_165, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_161])).
% 4.07/2.06  tff(c_108, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_96])).
% 4.07/2.06  tff(c_116, plain, (k4_xboole_0('#skF_3', k1_zfmisc_1('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_14])).
% 4.07/2.06  tff(c_270, plain, (v1_xboole_0('#skF_3') | k4_xboole_0('#skF_3', k1_zfmisc_1('#skF_1'))!='#skF_3'), inference(resolution, [status(thm)], [c_108, c_264])).
% 4.07/2.06  tff(c_285, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_270])).
% 4.07/2.06  tff(c_286, plain, (k1_xboole_0!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_165, c_285])).
% 4.07/2.06  tff(c_324, plain, (![A_64, B_65]: (k6_setfam_1(A_64, B_65)=k1_setfam_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.07/2.06  tff(c_337, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_324])).
% 4.07/2.06  tff(c_449, plain, (![A_70, B_71]: (k8_setfam_1(A_70, B_71)=k6_setfam_1(A_70, B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.07/2.06  tff(c_463, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_449])).
% 4.07/2.06  tff(c_470, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_463])).
% 4.07/2.06  tff(c_471, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_286, c_470])).
% 4.07/2.06  tff(c_336, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_324])).
% 4.07/2.06  tff(c_460, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_449])).
% 4.07/2.06  tff(c_467, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_460])).
% 4.07/2.06  tff(c_468, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_294, c_467])).
% 4.07/2.06  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.07/2.06  tff(c_473, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_40])).
% 4.07/2.06  tff(c_490, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_473])).
% 4.07/2.06  tff(c_493, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_490])).
% 4.07/2.06  tff(c_499, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_493])).
% 4.07/2.06  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_499])).
% 4.07/2.06  tff(c_503, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_288])).
% 4.07/2.06  tff(c_708, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)='#skF_2' | ~r1_tarski(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_14])).
% 4.07/2.06  tff(c_728, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_612, c_708])).
% 4.07/2.06  tff(c_36, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.07/2.06  tff(c_211, plain, (![A_53]: (k8_setfam_1(A_53, k1_xboole_0)=A_53 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.07/2.06  tff(c_215, plain, (![A_53]: (k8_setfam_1(A_53, k1_xboole_0)=A_53 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_36, c_211])).
% 4.07/2.06  tff(c_886, plain, (![A_94]: (k8_setfam_1(A_94, '#skF_2')=A_94 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_503, c_215])).
% 4.07/2.06  tff(c_894, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_107, c_886])).
% 4.07/2.06  tff(c_508, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_286])).
% 4.07/2.06  tff(c_28, plain, (![A_16, B_17]: (k8_setfam_1(A_16, B_17)=k6_setfam_1(A_16, B_17) | k1_xboole_0=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.07/2.06  tff(c_651, plain, (![A_79, B_80]: (k8_setfam_1(A_79, B_80)=k6_setfam_1(A_79, B_80) | B_80='#skF_2' | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_28])).
% 4.07/2.06  tff(c_665, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_44, c_651])).
% 4.07/2.06  tff(c_672, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_558, c_665])).
% 4.07/2.06  tff(c_673, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_508, c_672])).
% 4.07/2.06  tff(c_73, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.07/2.06  tff(c_80, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_40])).
% 4.07/2.06  tff(c_517, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_80])).
% 4.07/2.06  tff(c_674, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_517])).
% 4.07/2.06  tff(c_895, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_894, c_674])).
% 4.07/2.06  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_728, c_895])).
% 4.07/2.06  tff(c_901, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_161])).
% 4.07/2.06  tff(c_18, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.07/2.06  tff(c_909, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_901, c_18])).
% 4.07/2.06  tff(c_900, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_161])).
% 4.07/2.06  tff(c_905, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_900, c_18])).
% 4.07/2.06  tff(c_927, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_909, c_905])).
% 4.07/2.06  tff(c_935, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_40])).
% 4.07/2.06  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_935])).
% 4.07/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/2.06  
% 4.07/2.06  Inference rules
% 4.07/2.06  ----------------------
% 4.07/2.06  #Ref     : 0
% 4.07/2.06  #Sup     : 217
% 4.07/2.06  #Fact    : 0
% 4.07/2.06  #Define  : 0
% 4.07/2.06  #Split   : 10
% 4.07/2.06  #Chain   : 0
% 4.07/2.06  #Close   : 0
% 4.07/2.06  
% 4.07/2.06  Ordering : KBO
% 4.07/2.06  
% 4.07/2.06  Simplification rules
% 4.07/2.06  ----------------------
% 4.07/2.06  #Subsume      : 27
% 4.07/2.06  #Demod        : 87
% 4.07/2.06  #Tautology    : 94
% 4.07/2.06  #SimpNegUnit  : 10
% 4.07/2.06  #BackRed      : 37
% 4.07/2.06  
% 4.07/2.06  #Partial instantiations: 0
% 4.07/2.06  #Strategies tried      : 1
% 4.07/2.06  
% 4.07/2.06  Timing (in seconds)
% 4.07/2.06  ----------------------
% 4.07/2.07  Preprocessing        : 0.50
% 4.07/2.07  Parsing              : 0.26
% 4.07/2.07  CNF conversion       : 0.03
% 4.07/2.07  Main loop            : 0.64
% 4.07/2.07  Inferencing          : 0.23
% 4.07/2.07  Reduction            : 0.20
% 4.07/2.07  Demodulation         : 0.14
% 4.07/2.07  BG Simplification    : 0.03
% 4.07/2.07  Subsumption          : 0.11
% 4.07/2.07  Abstraction          : 0.03
% 4.07/2.07  MUC search           : 0.00
% 4.07/2.07  Cooper               : 0.00
% 4.07/2.07  Total                : 1.21
% 4.07/2.07  Index Insertion      : 0.00
% 4.07/2.07  Index Deletion       : 0.00
% 4.07/2.07  Index Matching       : 0.00
% 4.07/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
