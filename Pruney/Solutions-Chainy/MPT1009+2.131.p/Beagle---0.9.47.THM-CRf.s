%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 6.18s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 305 expanded)
%              Number of leaves         :   46 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 630 expanded)
%              Number of equality atoms :   49 ( 130 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [A_39,B_40] : v1_relat_1(k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4410,plain,(
    ! [B_408,A_409] :
      ( v1_relat_1(B_408)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(A_409))
      | ~ v1_relat_1(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4413,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_4410])).

tff(c_4416,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4413])).

tff(c_50,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k7_relat_1(B_50,A_49),B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) = k1_xboole_0
      | k1_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4423,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4416,c_48])).

tff(c_4425,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4423])).

tff(c_5031,plain,(
    ! [A_471,B_472,C_473,D_474] :
      ( k7_relset_1(A_471,B_472,C_473,D_474) = k9_relat_1(C_473,D_474)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5034,plain,(
    ! [D_474] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_474) = k9_relat_1('#skF_4',D_474) ),
    inference(resolution,[status(thm)],[c_66,c_5031])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4904,plain,(
    ! [B_462,A_463] :
      ( k1_tarski(k1_funct_1(B_462,A_463)) = k2_relat_1(B_462)
      | k1_tarski(A_463) != k1_relat_1(B_462)
      | ~ v1_funct_1(B_462)
      | ~ v1_relat_1(B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4913,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4904,c_62])).

tff(c_4919,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_70,c_4913])).

tff(c_5051,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5034,c_4919])).

tff(c_5052,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5051])).

tff(c_4529,plain,(
    ! [C_428,A_429,B_430] :
      ( v4_relat_1(C_428,A_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4533,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_4529])).

tff(c_34,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_relat_1(B_38),A_37)
      | ~ v4_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4497,plain,(
    ! [B_423,A_424] :
      ( k1_tarski(B_423) = A_424
      | k1_xboole_0 = A_424
      | ~ r1_tarski(A_424,k1_tarski(B_423)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5088,plain,(
    ! [B_485,B_486] :
      ( k1_tarski(B_485) = k1_relat_1(B_486)
      | k1_relat_1(B_486) = k1_xboole_0
      | ~ v4_relat_1(B_486,k1_tarski(B_485))
      | ~ v1_relat_1(B_486) ) ),
    inference(resolution,[status(thm)],[c_34,c_4497])).

tff(c_5094,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4533,c_5088])).

tff(c_5101,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_5094])).

tff(c_5103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4425,c_5052,c_5101])).

tff(c_5105,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5051])).

tff(c_52,plain,(
    ! [B_52,A_51] :
      ( k1_tarski(k1_funct_1(B_52,A_51)) = k2_relat_1(B_52)
      | k1_tarski(A_51) != k1_relat_1(B_52)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5035,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5034,c_62])).

tff(c_5047,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5035])).

tff(c_5049,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_70,c_5047])).

tff(c_5050,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5049])).

tff(c_5127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5105,c_5050])).

tff(c_5129,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5049])).

tff(c_5134,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5129,c_66])).

tff(c_5313,plain,(
    ! [A_496,B_497,C_498,D_499] :
      ( m1_subset_1(A_496,k1_zfmisc_1(k2_zfmisc_1(B_497,C_498)))
      | ~ r1_tarski(A_496,D_499)
      | ~ m1_subset_1(D_499,k1_zfmisc_1(k2_zfmisc_1(B_497,C_498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5702,plain,(
    ! [B_535,A_536,B_537,C_538] :
      ( m1_subset_1(k7_relat_1(B_535,A_536),k1_zfmisc_1(k2_zfmisc_1(B_537,C_538)))
      | ~ m1_subset_1(B_535,k1_zfmisc_1(k2_zfmisc_1(B_537,C_538)))
      | ~ v1_relat_1(B_535) ) ),
    inference(resolution,[status(thm)],[c_50,c_5313])).

tff(c_30,plain,(
    ! [B_36,A_34] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5715,plain,(
    ! [B_535,A_536,B_537,C_538] :
      ( v1_relat_1(k7_relat_1(B_535,A_536))
      | ~ v1_relat_1(k2_zfmisc_1(B_537,C_538))
      | ~ m1_subset_1(B_535,k1_zfmisc_1(k2_zfmisc_1(B_537,C_538)))
      | ~ v1_relat_1(B_535) ) ),
    inference(resolution,[status(thm)],[c_5702,c_30])).

tff(c_5739,plain,(
    ! [B_539,A_540,B_541,C_542] :
      ( v1_relat_1(k7_relat_1(B_539,A_540))
      | ~ m1_subset_1(B_539,k1_zfmisc_1(k2_zfmisc_1(B_541,C_542)))
      | ~ v1_relat_1(B_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5715])).

tff(c_5745,plain,(
    ! [A_540] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_540))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5134,c_5739])).

tff(c_5752,plain,(
    ! [A_540] : v1_relat_1(k7_relat_1('#skF_4',A_540)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_5745])).

tff(c_38,plain,(
    ! [B_42,A_41] :
      ( k2_relat_1(k7_relat_1(B_42,A_41)) = k9_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4730,plain,(
    ! [A_448,B_449] :
      ( r1_tarski(k2_relat_1(A_448),k2_relat_1(B_449))
      | ~ r1_tarski(A_448,B_449)
      | ~ v1_relat_1(B_449)
      | ~ v1_relat_1(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8143,plain,(
    ! [B_601,A_602,B_603] :
      ( r1_tarski(k9_relat_1(B_601,A_602),k2_relat_1(B_603))
      | ~ r1_tarski(k7_relat_1(B_601,A_602),B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_relat_1(k7_relat_1(B_601,A_602))
      | ~ v1_relat_1(B_601) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4730])).

tff(c_5128,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5049])).

tff(c_8152,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8143,c_5128])).

tff(c_8196,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_5752,c_8152])).

tff(c_8216,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_8196])).

tff(c_8220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_8216])).

tff(c_8221,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4423])).

tff(c_8222,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4423])).

tff(c_8307,plain,(
    ! [B_617,A_618] :
      ( v4_relat_1(B_617,A_618)
      | ~ r1_tarski(k1_relat_1(B_617),A_618)
      | ~ v1_relat_1(B_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8313,plain,(
    ! [A_618] :
      ( v4_relat_1('#skF_4',A_618)
      | ~ r1_tarski(k1_xboole_0,A_618)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8222,c_8307])).

tff(c_8327,plain,(
    ! [A_619] : v4_relat_1('#skF_4',A_619) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_8,c_8313])).

tff(c_40,plain,(
    ! [B_44,A_43] :
      ( k7_relat_1(B_44,A_43) = B_44
      | ~ v4_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8334,plain,(
    ! [A_619] :
      ( k7_relat_1('#skF_4',A_619) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8327,c_40])).

tff(c_8341,plain,(
    ! [A_620] : k7_relat_1('#skF_4',A_620) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_8334])).

tff(c_8346,plain,(
    ! [A_620] :
      ( k9_relat_1('#skF_4',A_620) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8341,c_38])).

tff(c_8354,plain,(
    ! [A_620] : k9_relat_1('#skF_4',A_620) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_8221,c_8346])).

tff(c_8996,plain,(
    ! [A_666,B_667,C_668,D_669] :
      ( k7_relset_1(A_666,B_667,C_668,D_669) = k9_relat_1(C_668,D_669)
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(A_666,B_667))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8998,plain,(
    ! [D_669] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_669) = k9_relat_1('#skF_4',D_669) ),
    inference(resolution,[status(thm)],[c_66,c_8996])).

tff(c_9000,plain,(
    ! [D_669] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_669) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8354,c_8998])).

tff(c_9001,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9000,c_62])).

tff(c_9004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.18/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.40  
% 6.47/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.47/2.40  
% 6.47/2.40  %Foreground sorts:
% 6.47/2.40  
% 6.47/2.40  
% 6.47/2.40  %Background operators:
% 6.47/2.40  
% 6.47/2.40  
% 6.47/2.40  %Foreground operators:
% 6.47/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.47/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.47/2.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.47/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.47/2.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.47/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.47/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.47/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.47/2.40  tff('#skF_1', type, '#skF_1': $i).
% 6.47/2.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.47/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.47/2.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.47/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.47/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.47/2.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.47/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.40  
% 6.47/2.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.47/2.42  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.47/2.42  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.47/2.42  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.47/2.42  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 6.47/2.42  tff(f_95, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.47/2.42  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.47/2.42  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.47/2.42  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.47/2.42  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.47/2.42  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.47/2.42  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 6.47/2.42  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.47/2.42  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.47/2.42  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.47/2.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.47/2.42  tff(c_36, plain, (![A_39, B_40]: (v1_relat_1(k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.42  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.47/2.42  tff(c_4410, plain, (![B_408, A_409]: (v1_relat_1(B_408) | ~m1_subset_1(B_408, k1_zfmisc_1(A_409)) | ~v1_relat_1(A_409))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.47/2.42  tff(c_4413, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_4410])).
% 6.47/2.42  tff(c_4416, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4413])).
% 6.47/2.42  tff(c_50, plain, (![B_50, A_49]: (r1_tarski(k7_relat_1(B_50, A_49), B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.42  tff(c_48, plain, (![A_48]: (k2_relat_1(A_48)=k1_xboole_0 | k1_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.47/2.42  tff(c_4423, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4416, c_48])).
% 6.47/2.42  tff(c_4425, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4423])).
% 6.47/2.42  tff(c_5031, plain, (![A_471, B_472, C_473, D_474]: (k7_relset_1(A_471, B_472, C_473, D_474)=k9_relat_1(C_473, D_474) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.47/2.42  tff(c_5034, plain, (![D_474]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_474)=k9_relat_1('#skF_4', D_474))), inference(resolution, [status(thm)], [c_66, c_5031])).
% 6.47/2.42  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.47/2.42  tff(c_4904, plain, (![B_462, A_463]: (k1_tarski(k1_funct_1(B_462, A_463))=k2_relat_1(B_462) | k1_tarski(A_463)!=k1_relat_1(B_462) | ~v1_funct_1(B_462) | ~v1_relat_1(B_462))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.47/2.42  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.47/2.42  tff(c_4913, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4904, c_62])).
% 6.47/2.42  tff(c_4919, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_70, c_4913])).
% 6.47/2.42  tff(c_5051, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5034, c_4919])).
% 6.47/2.42  tff(c_5052, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5051])).
% 6.47/2.42  tff(c_4529, plain, (![C_428, A_429, B_430]: (v4_relat_1(C_428, A_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.47/2.42  tff(c_4533, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4529])).
% 6.47/2.42  tff(c_34, plain, (![B_38, A_37]: (r1_tarski(k1_relat_1(B_38), A_37) | ~v4_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.42  tff(c_4497, plain, (![B_423, A_424]: (k1_tarski(B_423)=A_424 | k1_xboole_0=A_424 | ~r1_tarski(A_424, k1_tarski(B_423)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.42  tff(c_5088, plain, (![B_485, B_486]: (k1_tarski(B_485)=k1_relat_1(B_486) | k1_relat_1(B_486)=k1_xboole_0 | ~v4_relat_1(B_486, k1_tarski(B_485)) | ~v1_relat_1(B_486))), inference(resolution, [status(thm)], [c_34, c_4497])).
% 6.47/2.42  tff(c_5094, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4533, c_5088])).
% 6.47/2.42  tff(c_5101, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_5094])).
% 6.47/2.42  tff(c_5103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4425, c_5052, c_5101])).
% 6.47/2.42  tff(c_5105, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_5051])).
% 6.47/2.42  tff(c_52, plain, (![B_52, A_51]: (k1_tarski(k1_funct_1(B_52, A_51))=k2_relat_1(B_52) | k1_tarski(A_51)!=k1_relat_1(B_52) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.47/2.42  tff(c_5035, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5034, c_62])).
% 6.47/2.42  tff(c_5047, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52, c_5035])).
% 6.47/2.42  tff(c_5049, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_70, c_5047])).
% 6.47/2.42  tff(c_5050, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5049])).
% 6.47/2.42  tff(c_5127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5105, c_5050])).
% 6.47/2.42  tff(c_5129, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_5049])).
% 6.47/2.42  tff(c_5134, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5129, c_66])).
% 6.47/2.42  tff(c_5313, plain, (![A_496, B_497, C_498, D_499]: (m1_subset_1(A_496, k1_zfmisc_1(k2_zfmisc_1(B_497, C_498))) | ~r1_tarski(A_496, D_499) | ~m1_subset_1(D_499, k1_zfmisc_1(k2_zfmisc_1(B_497, C_498))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.47/2.42  tff(c_5702, plain, (![B_535, A_536, B_537, C_538]: (m1_subset_1(k7_relat_1(B_535, A_536), k1_zfmisc_1(k2_zfmisc_1(B_537, C_538))) | ~m1_subset_1(B_535, k1_zfmisc_1(k2_zfmisc_1(B_537, C_538))) | ~v1_relat_1(B_535))), inference(resolution, [status(thm)], [c_50, c_5313])).
% 6.47/2.42  tff(c_30, plain, (![B_36, A_34]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.47/2.42  tff(c_5715, plain, (![B_535, A_536, B_537, C_538]: (v1_relat_1(k7_relat_1(B_535, A_536)) | ~v1_relat_1(k2_zfmisc_1(B_537, C_538)) | ~m1_subset_1(B_535, k1_zfmisc_1(k2_zfmisc_1(B_537, C_538))) | ~v1_relat_1(B_535))), inference(resolution, [status(thm)], [c_5702, c_30])).
% 6.47/2.42  tff(c_5739, plain, (![B_539, A_540, B_541, C_542]: (v1_relat_1(k7_relat_1(B_539, A_540)) | ~m1_subset_1(B_539, k1_zfmisc_1(k2_zfmisc_1(B_541, C_542))) | ~v1_relat_1(B_539))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5715])).
% 6.47/2.42  tff(c_5745, plain, (![A_540]: (v1_relat_1(k7_relat_1('#skF_4', A_540)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5134, c_5739])).
% 6.47/2.42  tff(c_5752, plain, (![A_540]: (v1_relat_1(k7_relat_1('#skF_4', A_540)))), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_5745])).
% 6.47/2.42  tff(c_38, plain, (![B_42, A_41]: (k2_relat_1(k7_relat_1(B_42, A_41))=k9_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.47/2.42  tff(c_4730, plain, (![A_448, B_449]: (r1_tarski(k2_relat_1(A_448), k2_relat_1(B_449)) | ~r1_tarski(A_448, B_449) | ~v1_relat_1(B_449) | ~v1_relat_1(A_448))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.47/2.42  tff(c_8143, plain, (![B_601, A_602, B_603]: (r1_tarski(k9_relat_1(B_601, A_602), k2_relat_1(B_603)) | ~r1_tarski(k7_relat_1(B_601, A_602), B_603) | ~v1_relat_1(B_603) | ~v1_relat_1(k7_relat_1(B_601, A_602)) | ~v1_relat_1(B_601))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4730])).
% 6.47/2.42  tff(c_5128, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5049])).
% 6.47/2.42  tff(c_8152, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8143, c_5128])).
% 6.47/2.42  tff(c_8196, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_5752, c_8152])).
% 6.47/2.42  tff(c_8216, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_8196])).
% 6.47/2.42  tff(c_8220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4416, c_8216])).
% 6.47/2.42  tff(c_8221, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4423])).
% 6.47/2.42  tff(c_8222, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4423])).
% 6.47/2.42  tff(c_8307, plain, (![B_617, A_618]: (v4_relat_1(B_617, A_618) | ~r1_tarski(k1_relat_1(B_617), A_618) | ~v1_relat_1(B_617))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.42  tff(c_8313, plain, (![A_618]: (v4_relat_1('#skF_4', A_618) | ~r1_tarski(k1_xboole_0, A_618) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8222, c_8307])).
% 6.47/2.42  tff(c_8327, plain, (![A_619]: (v4_relat_1('#skF_4', A_619))), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_8, c_8313])).
% 6.47/2.42  tff(c_40, plain, (![B_44, A_43]: (k7_relat_1(B_44, A_43)=B_44 | ~v4_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.47/2.42  tff(c_8334, plain, (![A_619]: (k7_relat_1('#skF_4', A_619)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8327, c_40])).
% 6.47/2.42  tff(c_8341, plain, (![A_620]: (k7_relat_1('#skF_4', A_620)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_8334])).
% 6.47/2.42  tff(c_8346, plain, (![A_620]: (k9_relat_1('#skF_4', A_620)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8341, c_38])).
% 6.47/2.42  tff(c_8354, plain, (![A_620]: (k9_relat_1('#skF_4', A_620)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_8221, c_8346])).
% 6.47/2.42  tff(c_8996, plain, (![A_666, B_667, C_668, D_669]: (k7_relset_1(A_666, B_667, C_668, D_669)=k9_relat_1(C_668, D_669) | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(A_666, B_667))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.47/2.42  tff(c_8998, plain, (![D_669]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_669)=k9_relat_1('#skF_4', D_669))), inference(resolution, [status(thm)], [c_66, c_8996])).
% 6.47/2.42  tff(c_9000, plain, (![D_669]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_669)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8354, c_8998])).
% 6.47/2.42  tff(c_9001, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9000, c_62])).
% 6.47/2.42  tff(c_9004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_9001])).
% 6.47/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.42  
% 6.47/2.42  Inference rules
% 6.47/2.42  ----------------------
% 6.47/2.42  #Ref     : 0
% 6.47/2.42  #Sup     : 1781
% 6.47/2.42  #Fact    : 1
% 6.47/2.42  #Define  : 0
% 6.47/2.42  #Split   : 11
% 6.47/2.42  #Chain   : 0
% 6.47/2.42  #Close   : 0
% 6.47/2.42  
% 6.47/2.42  Ordering : KBO
% 6.47/2.42  
% 6.47/2.42  Simplification rules
% 6.47/2.42  ----------------------
% 6.47/2.42  #Subsume      : 261
% 6.47/2.42  #Demod        : 1843
% 6.47/2.42  #Tautology    : 854
% 6.47/2.42  #SimpNegUnit  : 73
% 6.47/2.42  #BackRed      : 32
% 6.47/2.42  
% 6.47/2.42  #Partial instantiations: 0
% 6.47/2.42  #Strategies tried      : 1
% 6.47/2.42  
% 6.47/2.42  Timing (in seconds)
% 6.47/2.42  ----------------------
% 6.47/2.42  Preprocessing        : 0.33
% 6.47/2.42  Parsing              : 0.18
% 6.47/2.42  CNF conversion       : 0.02
% 6.47/2.42  Main loop            : 1.22
% 6.47/2.42  Inferencing          : 0.42
% 6.47/2.42  Reduction            : 0.41
% 6.47/2.42  Demodulation         : 0.30
% 6.47/2.42  BG Simplification    : 0.05
% 6.47/2.42  Subsumption          : 0.25
% 6.47/2.42  Abstraction          : 0.06
% 6.47/2.42  MUC search           : 0.00
% 6.47/2.42  Cooper               : 0.00
% 6.47/2.42  Total                : 1.59
% 6.47/2.42  Index Insertion      : 0.00
% 6.47/2.42  Index Deletion       : 0.00
% 6.47/2.42  Index Matching       : 0.00
% 6.47/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
