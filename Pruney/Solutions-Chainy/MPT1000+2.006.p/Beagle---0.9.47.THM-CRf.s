%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 777 expanded)
%              Number of leaves         :   46 ( 251 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (1767 expanded)
%              Number of equality atoms :   70 ( 856 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_757,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k8_relset_1(A_151,B_152,C_153,D_154) = k10_relat_1(C_153,D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_770,plain,(
    ! [D_154] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_154) = k10_relat_1('#skF_5',D_154) ),
    inference(resolution,[status(thm)],[c_66,c_757])).

tff(c_62,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_785,plain,(
    k10_relat_1('#skF_5','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_62])).

tff(c_32,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_276,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_282,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_276])).

tff(c_286,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_282])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_549,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_564,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_549])).

tff(c_911,plain,(
    ! [B_169,A_170,C_171] :
      ( k1_xboole_0 = B_169
      | k1_relset_1(A_170,B_169,C_171) = A_170
      | ~ v1_funct_2(C_171,A_170,B_169)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_927,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_911])).

tff(c_932,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_564,c_927])).

tff(c_933,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_932])).

tff(c_456,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_471,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_456])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_480,plain,(
    ! [B_117,A_118] :
      ( k5_relat_1(B_117,k6_relat_1(A_118)) = B_117
      | ~ r1_tarski(k2_relat_1(B_117),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_495,plain,(
    ! [B_19,A_18] :
      ( k5_relat_1(B_19,k6_relat_1(A_18)) = B_19
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_480])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_611,plain,(
    ! [A_134,B_135] :
      ( k10_relat_1(A_134,k1_relat_1(B_135)) = k1_relat_1(k5_relat_1(A_134,B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_629,plain,(
    ! [A_134,A_27] :
      ( k1_relat_1(k5_relat_1(A_134,k6_relat_1(A_27))) = k10_relat_1(A_134,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_611])).

tff(c_1101,plain,(
    ! [A_182,A_183] :
      ( k1_relat_1(k5_relat_1(A_182,k6_relat_1(A_183))) = k10_relat_1(A_182,A_183)
      | ~ v1_relat_1(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_629])).

tff(c_5730,plain,(
    ! [B_414,A_415] :
      ( k10_relat_1(B_414,A_415) = k1_relat_1(B_414)
      | ~ v1_relat_1(B_414)
      | ~ v5_relat_1(B_414,A_415)
      | ~ v1_relat_1(B_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_1101])).

tff(c_5790,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_471,c_5730])).

tff(c_5831,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_933,c_5790])).

tff(c_5833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_5831])).

tff(c_5835,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5834,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5841,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5835,c_5834])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5836,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5834,c_12])).

tff(c_5847,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5841,c_5836])).

tff(c_5913,plain,(
    ! [A_427,B_428] :
      ( v1_xboole_0(k2_zfmisc_1(A_427,B_428))
      | ~ v1_xboole_0(B_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5861,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5835,c_14])).

tff(c_5922,plain,(
    ! [A_429,B_430] :
      ( k2_zfmisc_1(A_429,B_430) = '#skF_4'
      | ~ v1_xboole_0(B_430) ) ),
    inference(resolution,[status(thm)],[c_5913,c_5861])).

tff(c_5933,plain,(
    ! [A_431] : k2_zfmisc_1(A_431,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5847,c_5922])).

tff(c_5940,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5933,c_32])).

tff(c_5878,plain,(
    ! [A_421] :
      ( v1_xboole_0(k1_relat_1(A_421))
      | ~ v1_xboole_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5888,plain,(
    ! [A_424] :
      ( k1_relat_1(A_424) = '#skF_4'
      | ~ v1_xboole_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_5878,c_5861])).

tff(c_5896,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5847,c_5888])).

tff(c_6047,plain,(
    ! [A_446,B_447] :
      ( r2_hidden('#skF_2'(A_446,B_447),A_446)
      | r1_tarski(A_446,B_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6055,plain,(
    ! [A_446] : r1_tarski(A_446,A_446) ),
    inference(resolution,[status(thm)],[c_6047,c_8])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5931,plain,(
    ! [A_429] : k2_zfmisc_1(A_429,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5847,c_5922])).

tff(c_50,plain,(
    ! [A_40] :
      ( v1_funct_2(k1_xboole_0,A_40,k1_xboole_0)
      | k1_xboole_0 = A_40
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_40,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6308,plain,(
    ! [A_40] :
      ( v1_funct_2('#skF_4',A_40,'#skF_4')
      | A_40 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5931,c_5835,c_5835,c_5835,c_5835,c_5835,c_50])).

tff(c_6309,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6308])).

tff(c_6312,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_6309])).

tff(c_6316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6055,c_6312])).

tff(c_6318,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6308])).

tff(c_6202,plain,(
    ! [C_470,B_471,A_472] :
      ( v5_relat_1(C_470,B_471)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_472,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6215,plain,(
    ! [C_470] :
      ( v5_relat_1(C_470,'#skF_4')
      | ~ m1_subset_1(C_470,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5931,c_6202])).

tff(c_6331,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6318,c_6215])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6119,plain,(
    ! [C_458,B_459,A_460] :
      ( r2_hidden(C_458,B_459)
      | ~ r2_hidden(C_458,A_460)
      | ~ r1_tarski(A_460,B_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6553,plain,(
    ! [A_530,B_531] :
      ( r2_hidden('#skF_1'(A_530),B_531)
      | ~ r1_tarski(A_530,B_531)
      | v1_xboole_0(A_530) ) ),
    inference(resolution,[status(thm)],[c_4,c_6119])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6561,plain,(
    ! [B_532,A_533] :
      ( ~ v1_xboole_0(B_532)
      | ~ r1_tarski(A_533,B_532)
      | v1_xboole_0(A_533) ) ),
    inference(resolution,[status(thm)],[c_6553,c_2])).

tff(c_7115,plain,(
    ! [A_572,B_573] :
      ( ~ v1_xboole_0(A_572)
      | v1_xboole_0(k2_relat_1(B_573))
      | ~ v5_relat_1(B_573,A_572)
      | ~ v1_relat_1(B_573) ) ),
    inference(resolution,[status(thm)],[c_26,c_6561])).

tff(c_7129,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6331,c_7115])).

tff(c_7154,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_5847,c_7129])).

tff(c_6056,plain,(
    ! [A_446,B_447] :
      ( ~ v1_xboole_0(A_446)
      | r1_tarski(A_446,B_447) ) ),
    inference(resolution,[status(thm)],[c_6047,c_2])).

tff(c_6281,plain,(
    ! [B_485,A_486] :
      ( k5_relat_1(B_485,k6_relat_1(A_486)) = B_485
      | ~ r1_tarski(k2_relat_1(B_485),A_486)
      | ~ v1_relat_1(B_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6297,plain,(
    ! [B_485,B_447] :
      ( k5_relat_1(B_485,k6_relat_1(B_447)) = B_485
      | ~ v1_relat_1(B_485)
      | ~ v1_xboole_0(k2_relat_1(B_485)) ) ),
    inference(resolution,[status(thm)],[c_6056,c_6281])).

tff(c_7166,plain,(
    ! [B_447] :
      ( k5_relat_1('#skF_4',k6_relat_1(B_447)) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7154,c_6297])).

tff(c_7294,plain,(
    ! [B_579] : k5_relat_1('#skF_4',k6_relat_1(B_579)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_7166])).

tff(c_6393,plain,(
    ! [A_503,B_504] :
      ( k10_relat_1(A_503,k1_relat_1(B_504)) = k1_relat_1(k5_relat_1(A_503,B_504))
      | ~ v1_relat_1(B_504)
      | ~ v1_relat_1(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6411,plain,(
    ! [A_503,A_27] :
      ( k1_relat_1(k5_relat_1(A_503,k6_relat_1(A_27))) = k10_relat_1(A_503,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(A_503) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6393])).

tff(c_6419,plain,(
    ! [A_503,A_27] :
      ( k1_relat_1(k5_relat_1(A_503,k6_relat_1(A_27))) = k10_relat_1(A_503,A_27)
      | ~ v1_relat_1(A_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6411])).

tff(c_7299,plain,(
    ! [B_579] :
      ( k10_relat_1('#skF_4',B_579) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7294,c_6419])).

tff(c_7319,plain,(
    ! [B_579] : k10_relat_1('#skF_4',B_579) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_5896,c_7299])).

tff(c_6182,plain,(
    ! [B_468,A_469] :
      ( v5_relat_1(B_468,A_469)
      | ~ r1_tarski(k2_relat_1(B_468),A_469)
      | ~ v1_relat_1(B_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6198,plain,(
    ! [B_468,B_447] :
      ( v5_relat_1(B_468,B_447)
      | ~ v1_relat_1(B_468)
      | ~ v1_xboole_0(k2_relat_1(B_468)) ) ),
    inference(resolution,[status(thm)],[c_6056,c_6182])).

tff(c_7168,plain,(
    ! [B_447] :
      ( v5_relat_1('#skF_4',B_447)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7154,c_6198])).

tff(c_7185,plain,(
    ! [B_447] : v5_relat_1('#skF_4',B_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_7168])).

tff(c_7190,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7154,c_5861])).

tff(c_7235,plain,(
    ! [A_18] :
      ( r1_tarski('#skF_4',A_18)
      | ~ v5_relat_1('#skF_4',A_18)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7190,c_26])).

tff(c_7255,plain,(
    ! [A_18] : r1_tarski('#skF_4',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_7185,c_7235])).

tff(c_6514,plain,(
    ! [A_522,B_523,C_524,D_525] :
      ( k8_relset_1(A_522,B_523,C_524,D_525) = k10_relat_1(C_524,D_525)
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_522,B_523))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7706,plain,(
    ! [A_603,B_604,A_605,D_606] :
      ( k8_relset_1(A_603,B_604,A_605,D_606) = k10_relat_1(A_605,D_606)
      | ~ r1_tarski(A_605,k2_zfmisc_1(A_603,B_604)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6514])).

tff(c_7709,plain,(
    ! [A_603,B_604,D_606] : k8_relset_1(A_603,B_604,'#skF_4',D_606) = k10_relat_1('#skF_4',D_606) ),
    inference(resolution,[status(thm)],[c_7255,c_7706])).

tff(c_7726,plain,(
    ! [A_603,B_604,D_606] : k8_relset_1(A_603,B_604,'#skF_4',D_606) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7319,c_7709])).

tff(c_5887,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5841,c_66])).

tff(c_5932,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5931,c_5887])).

tff(c_5978,plain,(
    ! [A_436,B_437] :
      ( r1_tarski(A_436,B_437)
      | ~ m1_subset_1(A_436,k1_zfmisc_1(B_437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5986,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5932,c_5978])).

tff(c_6573,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5986,c_6561])).

tff(c_6579,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6573])).

tff(c_6614,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6579,c_5861])).

tff(c_5907,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5841,c_5841,c_62])).

tff(c_6621,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6614,c_5907])).

tff(c_7732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_6621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:44:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.49  
% 6.93/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.93/2.50  
% 6.93/2.50  %Foreground sorts:
% 6.93/2.50  
% 6.93/2.50  
% 6.93/2.50  %Background operators:
% 6.93/2.50  
% 6.93/2.50  
% 6.93/2.50  %Foreground operators:
% 6.93/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.93/2.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.93/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.93/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.93/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.93/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.93/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.93/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.93/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.93/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.93/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.93/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.93/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.93/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.93/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.93/2.50  
% 6.93/2.52  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 6.93/2.52  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.93/2.52  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.93/2.52  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.93/2.52  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.93/2.52  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.93/2.52  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.93/2.52  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.93/2.52  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 6.93/2.52  tff(f_66, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.93/2.52  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.93/2.52  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 6.93/2.52  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.93/2.52  tff(f_47, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 6.93/2.52  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.93/2.52  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 6.93/2.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.93/2.52  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.93/2.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.93/2.52  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.93/2.52  tff(c_757, plain, (![A_151, B_152, C_153, D_154]: (k8_relset_1(A_151, B_152, C_153, D_154)=k10_relat_1(C_153, D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.52  tff(c_770, plain, (![D_154]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_154)=k10_relat_1('#skF_5', D_154))), inference(resolution, [status(thm)], [c_66, c_757])).
% 6.93/2.52  tff(c_62, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.93/2.52  tff(c_785, plain, (k10_relat_1('#skF_5', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_62])).
% 6.93/2.52  tff(c_32, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.93/2.52  tff(c_276, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.93/2.52  tff(c_282, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_276])).
% 6.93/2.52  tff(c_286, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_282])).
% 6.93/2.52  tff(c_64, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.93/2.52  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 6.93/2.52  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.93/2.52  tff(c_549, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.93/2.52  tff(c_564, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_549])).
% 6.93/2.52  tff(c_911, plain, (![B_169, A_170, C_171]: (k1_xboole_0=B_169 | k1_relset_1(A_170, B_169, C_171)=A_170 | ~v1_funct_2(C_171, A_170, B_169) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.93/2.52  tff(c_927, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_911])).
% 6.93/2.52  tff(c_932, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_564, c_927])).
% 6.93/2.52  tff(c_933, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_932])).
% 6.93/2.52  tff(c_456, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.93/2.52  tff(c_471, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_456])).
% 6.93/2.52  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.93/2.52  tff(c_480, plain, (![B_117, A_118]: (k5_relat_1(B_117, k6_relat_1(A_118))=B_117 | ~r1_tarski(k2_relat_1(B_117), A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.93/2.52  tff(c_495, plain, (![B_19, A_18]: (k5_relat_1(B_19, k6_relat_1(A_18))=B_19 | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_26, c_480])).
% 6.93/2.52  tff(c_28, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.93/2.52  tff(c_36, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.93/2.52  tff(c_611, plain, (![A_134, B_135]: (k10_relat_1(A_134, k1_relat_1(B_135))=k1_relat_1(k5_relat_1(A_134, B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.93/2.52  tff(c_629, plain, (![A_134, A_27]: (k1_relat_1(k5_relat_1(A_134, k6_relat_1(A_27)))=k10_relat_1(A_134, A_27) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_36, c_611])).
% 6.93/2.52  tff(c_1101, plain, (![A_182, A_183]: (k1_relat_1(k5_relat_1(A_182, k6_relat_1(A_183)))=k10_relat_1(A_182, A_183) | ~v1_relat_1(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_629])).
% 6.93/2.52  tff(c_5730, plain, (![B_414, A_415]: (k10_relat_1(B_414, A_415)=k1_relat_1(B_414) | ~v1_relat_1(B_414) | ~v5_relat_1(B_414, A_415) | ~v1_relat_1(B_414))), inference(superposition, [status(thm), theory('equality')], [c_495, c_1101])).
% 6.93/2.52  tff(c_5790, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_471, c_5730])).
% 6.93/2.52  tff(c_5831, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_933, c_5790])).
% 6.93/2.52  tff(c_5833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_785, c_5831])).
% 6.93/2.52  tff(c_5835, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 6.93/2.52  tff(c_5834, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 6.93/2.52  tff(c_5841, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5835, c_5834])).
% 6.93/2.52  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.93/2.52  tff(c_5836, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5834, c_12])).
% 6.93/2.52  tff(c_5847, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5841, c_5836])).
% 6.93/2.52  tff(c_5913, plain, (![A_427, B_428]: (v1_xboole_0(k2_zfmisc_1(A_427, B_428)) | ~v1_xboole_0(B_428))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.93/2.52  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.52  tff(c_5861, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_5835, c_14])).
% 6.93/2.52  tff(c_5922, plain, (![A_429, B_430]: (k2_zfmisc_1(A_429, B_430)='#skF_4' | ~v1_xboole_0(B_430))), inference(resolution, [status(thm)], [c_5913, c_5861])).
% 6.93/2.52  tff(c_5933, plain, (![A_431]: (k2_zfmisc_1(A_431, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_5847, c_5922])).
% 6.93/2.52  tff(c_5940, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5933, c_32])).
% 6.93/2.52  tff(c_5878, plain, (![A_421]: (v1_xboole_0(k1_relat_1(A_421)) | ~v1_xboole_0(A_421))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.93/2.52  tff(c_5888, plain, (![A_424]: (k1_relat_1(A_424)='#skF_4' | ~v1_xboole_0(A_424))), inference(resolution, [status(thm)], [c_5878, c_5861])).
% 6.93/2.52  tff(c_5896, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5847, c_5888])).
% 6.93/2.52  tff(c_6047, plain, (![A_446, B_447]: (r2_hidden('#skF_2'(A_446, B_447), A_446) | r1_tarski(A_446, B_447))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.93/2.52  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.93/2.52  tff(c_6055, plain, (![A_446]: (r1_tarski(A_446, A_446))), inference(resolution, [status(thm)], [c_6047, c_8])).
% 6.93/2.52  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.93/2.52  tff(c_5931, plain, (![A_429]: (k2_zfmisc_1(A_429, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_5847, c_5922])).
% 6.93/2.52  tff(c_50, plain, (![A_40]: (v1_funct_2(k1_xboole_0, A_40, k1_xboole_0) | k1_xboole_0=A_40 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_40, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.93/2.52  tff(c_6308, plain, (![A_40]: (v1_funct_2('#skF_4', A_40, '#skF_4') | A_40='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5931, c_5835, c_5835, c_5835, c_5835, c_5835, c_50])).
% 6.93/2.52  tff(c_6309, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6308])).
% 6.93/2.52  tff(c_6312, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_6309])).
% 6.93/2.52  tff(c_6316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6055, c_6312])).
% 6.93/2.52  tff(c_6318, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6308])).
% 6.93/2.52  tff(c_6202, plain, (![C_470, B_471, A_472]: (v5_relat_1(C_470, B_471) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_472, B_471))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.93/2.52  tff(c_6215, plain, (![C_470]: (v5_relat_1(C_470, '#skF_4') | ~m1_subset_1(C_470, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5931, c_6202])).
% 6.93/2.52  tff(c_6331, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_6318, c_6215])).
% 6.93/2.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.52  tff(c_6119, plain, (![C_458, B_459, A_460]: (r2_hidden(C_458, B_459) | ~r2_hidden(C_458, A_460) | ~r1_tarski(A_460, B_459))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.93/2.52  tff(c_6553, plain, (![A_530, B_531]: (r2_hidden('#skF_1'(A_530), B_531) | ~r1_tarski(A_530, B_531) | v1_xboole_0(A_530))), inference(resolution, [status(thm)], [c_4, c_6119])).
% 6.93/2.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.52  tff(c_6561, plain, (![B_532, A_533]: (~v1_xboole_0(B_532) | ~r1_tarski(A_533, B_532) | v1_xboole_0(A_533))), inference(resolution, [status(thm)], [c_6553, c_2])).
% 6.93/2.52  tff(c_7115, plain, (![A_572, B_573]: (~v1_xboole_0(A_572) | v1_xboole_0(k2_relat_1(B_573)) | ~v5_relat_1(B_573, A_572) | ~v1_relat_1(B_573))), inference(resolution, [status(thm)], [c_26, c_6561])).
% 6.93/2.52  tff(c_7129, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6331, c_7115])).
% 6.93/2.52  tff(c_7154, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_5847, c_7129])).
% 6.93/2.52  tff(c_6056, plain, (![A_446, B_447]: (~v1_xboole_0(A_446) | r1_tarski(A_446, B_447))), inference(resolution, [status(thm)], [c_6047, c_2])).
% 6.93/2.52  tff(c_6281, plain, (![B_485, A_486]: (k5_relat_1(B_485, k6_relat_1(A_486))=B_485 | ~r1_tarski(k2_relat_1(B_485), A_486) | ~v1_relat_1(B_485))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.93/2.52  tff(c_6297, plain, (![B_485, B_447]: (k5_relat_1(B_485, k6_relat_1(B_447))=B_485 | ~v1_relat_1(B_485) | ~v1_xboole_0(k2_relat_1(B_485)))), inference(resolution, [status(thm)], [c_6056, c_6281])).
% 6.93/2.52  tff(c_7166, plain, (![B_447]: (k5_relat_1('#skF_4', k6_relat_1(B_447))='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7154, c_6297])).
% 6.93/2.52  tff(c_7294, plain, (![B_579]: (k5_relat_1('#skF_4', k6_relat_1(B_579))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_7166])).
% 6.93/2.52  tff(c_6393, plain, (![A_503, B_504]: (k10_relat_1(A_503, k1_relat_1(B_504))=k1_relat_1(k5_relat_1(A_503, B_504)) | ~v1_relat_1(B_504) | ~v1_relat_1(A_503))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.93/2.52  tff(c_6411, plain, (![A_503, A_27]: (k1_relat_1(k5_relat_1(A_503, k6_relat_1(A_27)))=k10_relat_1(A_503, A_27) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(A_503))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6393])).
% 6.93/2.52  tff(c_6419, plain, (![A_503, A_27]: (k1_relat_1(k5_relat_1(A_503, k6_relat_1(A_27)))=k10_relat_1(A_503, A_27) | ~v1_relat_1(A_503))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6411])).
% 6.93/2.52  tff(c_7299, plain, (![B_579]: (k10_relat_1('#skF_4', B_579)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7294, c_6419])).
% 6.93/2.52  tff(c_7319, plain, (![B_579]: (k10_relat_1('#skF_4', B_579)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_5896, c_7299])).
% 6.93/2.52  tff(c_6182, plain, (![B_468, A_469]: (v5_relat_1(B_468, A_469) | ~r1_tarski(k2_relat_1(B_468), A_469) | ~v1_relat_1(B_468))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.93/2.52  tff(c_6198, plain, (![B_468, B_447]: (v5_relat_1(B_468, B_447) | ~v1_relat_1(B_468) | ~v1_xboole_0(k2_relat_1(B_468)))), inference(resolution, [status(thm)], [c_6056, c_6182])).
% 6.93/2.52  tff(c_7168, plain, (![B_447]: (v5_relat_1('#skF_4', B_447) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7154, c_6198])).
% 6.93/2.52  tff(c_7185, plain, (![B_447]: (v5_relat_1('#skF_4', B_447))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_7168])).
% 6.93/2.52  tff(c_7190, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_7154, c_5861])).
% 6.93/2.52  tff(c_7235, plain, (![A_18]: (r1_tarski('#skF_4', A_18) | ~v5_relat_1('#skF_4', A_18) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7190, c_26])).
% 6.93/2.52  tff(c_7255, plain, (![A_18]: (r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_7185, c_7235])).
% 6.93/2.52  tff(c_6514, plain, (![A_522, B_523, C_524, D_525]: (k8_relset_1(A_522, B_523, C_524, D_525)=k10_relat_1(C_524, D_525) | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_522, B_523))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.52  tff(c_7706, plain, (![A_603, B_604, A_605, D_606]: (k8_relset_1(A_603, B_604, A_605, D_606)=k10_relat_1(A_605, D_606) | ~r1_tarski(A_605, k2_zfmisc_1(A_603, B_604)))), inference(resolution, [status(thm)], [c_20, c_6514])).
% 6.93/2.52  tff(c_7709, plain, (![A_603, B_604, D_606]: (k8_relset_1(A_603, B_604, '#skF_4', D_606)=k10_relat_1('#skF_4', D_606))), inference(resolution, [status(thm)], [c_7255, c_7706])).
% 6.93/2.52  tff(c_7726, plain, (![A_603, B_604, D_606]: (k8_relset_1(A_603, B_604, '#skF_4', D_606)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7319, c_7709])).
% 6.93/2.52  tff(c_5887, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5841, c_66])).
% 6.93/2.52  tff(c_5932, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5931, c_5887])).
% 6.93/2.52  tff(c_5978, plain, (![A_436, B_437]: (r1_tarski(A_436, B_437) | ~m1_subset_1(A_436, k1_zfmisc_1(B_437)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.93/2.52  tff(c_5986, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5932, c_5978])).
% 6.93/2.52  tff(c_6573, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5986, c_6561])).
% 6.93/2.52  tff(c_6579, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5847, c_6573])).
% 6.93/2.52  tff(c_6614, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6579, c_5861])).
% 6.93/2.52  tff(c_5907, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5841, c_5841, c_62])).
% 6.93/2.52  tff(c_6621, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6614, c_5907])).
% 6.93/2.52  tff(c_7732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7726, c_6621])).
% 6.93/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.52  
% 6.93/2.52  Inference rules
% 6.93/2.52  ----------------------
% 6.93/2.52  #Ref     : 0
% 6.93/2.52  #Sup     : 1692
% 6.93/2.52  #Fact    : 0
% 6.93/2.52  #Define  : 0
% 6.93/2.52  #Split   : 13
% 6.93/2.52  #Chain   : 0
% 6.93/2.52  #Close   : 0
% 6.93/2.52  
% 6.93/2.52  Ordering : KBO
% 6.93/2.52  
% 6.93/2.52  Simplification rules
% 6.93/2.52  ----------------------
% 6.93/2.52  #Subsume      : 432
% 6.93/2.52  #Demod        : 1416
% 6.93/2.52  #Tautology    : 810
% 6.93/2.52  #SimpNegUnit  : 75
% 6.93/2.52  #BackRed      : 59
% 6.93/2.52  
% 6.93/2.52  #Partial instantiations: 0
% 6.93/2.52  #Strategies tried      : 1
% 6.93/2.52  
% 6.93/2.52  Timing (in seconds)
% 6.93/2.52  ----------------------
% 6.93/2.52  Preprocessing        : 0.33
% 6.93/2.52  Parsing              : 0.17
% 6.93/2.52  CNF conversion       : 0.02
% 6.93/2.52  Main loop            : 1.42
% 6.93/2.52  Inferencing          : 0.47
% 6.93/2.52  Reduction            : 0.47
% 6.93/2.52  Demodulation         : 0.33
% 6.93/2.52  BG Simplification    : 0.05
% 6.93/2.52  Subsumption          : 0.33
% 6.93/2.52  Abstraction          : 0.06
% 6.93/2.52  MUC search           : 0.00
% 6.93/2.52  Cooper               : 0.00
% 6.93/2.52  Total                : 1.80
% 6.93/2.52  Index Insertion      : 0.00
% 6.93/2.52  Index Deletion       : 0.00
% 6.93/2.52  Index Matching       : 0.00
% 6.93/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
