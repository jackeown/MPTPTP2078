%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 620 expanded)
%              Number of leaves         :   46 ( 205 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 (1340 expanded)
%              Number of equality atoms :   68 ( 584 expanded)
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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_97,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
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

tff(f_68,axiom,(
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

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_847,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k8_relset_1(A_161,B_162,C_163,D_164) = k10_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_860,plain,(
    ! [D_164] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_164) = k10_relat_1('#skF_5',D_164) ),
    inference(resolution,[status(thm)],[c_68,c_847])).

tff(c_64,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_861,plain,(
    k10_relat_1('#skF_5','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_64])).

tff(c_30,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_279,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_285,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_279])).

tff(c_289,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_285])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_750,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_768,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_750])).

tff(c_1290,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_xboole_0 = B_194
      | k1_relset_1(A_195,B_194,C_196) = A_195
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1306,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1290])).

tff(c_1311,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_768,c_1306])).

tff(c_1312,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1311])).

tff(c_484,plain,(
    ! [C_110,B_111,A_112] :
      ( v5_relat_1(C_110,B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_502,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_484])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_598,plain,(
    ! [B_130,A_131] :
      ( k5_relat_1(B_130,k6_relat_1(A_131)) = B_130
      | ~ r1_tarski(k2_relat_1(B_130),A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_990,plain,(
    ! [B_177,A_178] :
      ( k5_relat_1(B_177,k6_relat_1(A_178)) = B_177
      | ~ v5_relat_1(B_177,A_178)
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_26,c_598])).

tff(c_40,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_684,plain,(
    ! [A_140,B_141] :
      ( k10_relat_1(A_140,k1_relat_1(B_141)) = k1_relat_1(k5_relat_1(A_140,B_141))
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_702,plain,(
    ! [A_140,A_26] :
      ( k1_relat_1(k5_relat_1(A_140,k6_relat_1(A_26))) = k10_relat_1(A_140,A_26)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_684])).

tff(c_710,plain,(
    ! [A_140,A_26] :
      ( k1_relat_1(k5_relat_1(A_140,k6_relat_1(A_26))) = k10_relat_1(A_140,A_26)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_702])).

tff(c_5748,plain,(
    ! [B_420,A_421] :
      ( k10_relat_1(B_420,A_421) = k1_relat_1(B_420)
      | ~ v1_relat_1(B_420)
      | ~ v5_relat_1(B_420,A_421)
      | ~ v1_relat_1(B_420) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_710])).

tff(c_5808,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_502,c_5748])).

tff(c_5849,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_1312,c_5808])).

tff(c_5851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_5849])).

tff(c_5853,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5852,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5859,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5853,c_5852])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5854,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5852,c_12])).

tff(c_5865,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_5854])).

tff(c_5931,plain,(
    ! [A_433,B_434] :
      ( v1_xboole_0(k2_zfmisc_1(A_433,B_434))
      | ~ v1_xboole_0(B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5890,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5853,c_14])).

tff(c_5940,plain,(
    ! [A_435,B_436] :
      ( k2_zfmisc_1(A_435,B_436) = '#skF_4'
      | ~ v1_xboole_0(B_436) ) ),
    inference(resolution,[status(thm)],[c_5931,c_5890])).

tff(c_5951,plain,(
    ! [A_437] : k2_zfmisc_1(A_437,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5865,c_5940])).

tff(c_5958,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5951,c_30])).

tff(c_5898,plain,(
    ! [A_429] :
      ( v1_xboole_0(k1_relat_1(A_429))
      | ~ v1_xboole_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5907,plain,(
    ! [A_430] :
      ( k1_relat_1(A_430) = '#skF_4'
      | ~ v1_xboole_0(A_430) ) ),
    inference(resolution,[status(thm)],[c_5898,c_5890])).

tff(c_5915,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5865,c_5907])).

tff(c_5949,plain,(
    ! [A_435] : k2_zfmisc_1(A_435,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5865,c_5940])).

tff(c_6065,plain,(
    ! [A_452,B_453] :
      ( r2_hidden('#skF_2'(A_452,B_453),A_452)
      | r1_tarski(A_452,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6073,plain,(
    ! [A_452] : r1_tarski(A_452,A_452) ),
    inference(resolution,[status(thm)],[c_6065,c_8])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6198,plain,(
    ! [C_481,B_482,A_483] :
      ( v5_relat_1(C_481,B_482)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_483,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6315,plain,(
    ! [A_502,B_503,A_504] :
      ( v5_relat_1(A_502,B_503)
      | ~ r1_tarski(A_502,k2_zfmisc_1(A_504,B_503)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6198])).

tff(c_6370,plain,(
    ! [A_509,B_510] : v5_relat_1(k2_zfmisc_1(A_509,B_510),B_510) ),
    inference(resolution,[status(thm)],[c_6073,c_6315])).

tff(c_6376,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5949,c_6370])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6103,plain,(
    ! [C_461,B_462,A_463] :
      ( r2_hidden(C_461,B_462)
      | ~ r2_hidden(C_461,A_463)
      | ~ r1_tarski(A_463,B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6557,plain,(
    ! [A_534,B_535] :
      ( r2_hidden('#skF_1'(A_534),B_535)
      | ~ r1_tarski(A_534,B_535)
      | v1_xboole_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_4,c_6103])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6565,plain,(
    ! [B_536,A_537] :
      ( ~ v1_xboole_0(B_536)
      | ~ r1_tarski(A_537,B_536)
      | v1_xboole_0(A_537) ) ),
    inference(resolution,[status(thm)],[c_6557,c_2])).

tff(c_7219,plain,(
    ! [A_585,B_586] :
      ( ~ v1_xboole_0(A_585)
      | v1_xboole_0(k2_relat_1(B_586))
      | ~ v5_relat_1(B_586,A_585)
      | ~ v1_relat_1(B_586) ) ),
    inference(resolution,[status(thm)],[c_26,c_6565])).

tff(c_7229,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6376,c_7219])).

tff(c_7254,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_5865,c_7229])).

tff(c_6074,plain,(
    ! [A_452,B_453] :
      ( ~ v1_xboole_0(A_452)
      | r1_tarski(A_452,B_453) ) ),
    inference(resolution,[status(thm)],[c_6065,c_2])).

tff(c_6267,plain,(
    ! [B_496,A_497] :
      ( k5_relat_1(B_496,k6_relat_1(A_497)) = B_496
      | ~ r1_tarski(k2_relat_1(B_496),A_497)
      | ~ v1_relat_1(B_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6283,plain,(
    ! [B_496,B_453] :
      ( k5_relat_1(B_496,k6_relat_1(B_453)) = B_496
      | ~ v1_relat_1(B_496)
      | ~ v1_xboole_0(k2_relat_1(B_496)) ) ),
    inference(resolution,[status(thm)],[c_6074,c_6267])).

tff(c_7270,plain,(
    ! [B_453] :
      ( k5_relat_1('#skF_4',k6_relat_1(B_453)) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7254,c_6283])).

tff(c_7453,plain,(
    ! [B_594] : k5_relat_1('#skF_4',k6_relat_1(B_594)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_7270])).

tff(c_6343,plain,(
    ! [A_507,B_508] :
      ( k10_relat_1(A_507,k1_relat_1(B_508)) = k1_relat_1(k5_relat_1(A_507,B_508))
      | ~ v1_relat_1(B_508)
      | ~ v1_relat_1(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6361,plain,(
    ! [A_507,A_26] :
      ( k1_relat_1(k5_relat_1(A_507,k6_relat_1(A_26))) = k10_relat_1(A_507,A_26)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(A_507) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6343])).

tff(c_6369,plain,(
    ! [A_507,A_26] :
      ( k1_relat_1(k5_relat_1(A_507,k6_relat_1(A_26))) = k10_relat_1(A_507,A_26)
      | ~ v1_relat_1(A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6361])).

tff(c_7458,plain,(
    ! [B_594] :
      ( k10_relat_1('#skF_4',B_594) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7453,c_6369])).

tff(c_7478,plain,(
    ! [B_594] : k10_relat_1('#skF_4',B_594) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_5915,c_7458])).

tff(c_6134,plain,(
    ! [B_465,A_466] :
      ( v5_relat_1(B_465,A_466)
      | ~ r1_tarski(k2_relat_1(B_465),A_466)
      | ~ v1_relat_1(B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6146,plain,(
    ! [B_465,B_453] :
      ( v5_relat_1(B_465,B_453)
      | ~ v1_relat_1(B_465)
      | ~ v1_xboole_0(k2_relat_1(B_465)) ) ),
    inference(resolution,[status(thm)],[c_6074,c_6134])).

tff(c_7272,plain,(
    ! [B_453] :
      ( v5_relat_1('#skF_4',B_453)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7254,c_6146])).

tff(c_7289,plain,(
    ! [B_453] : v5_relat_1('#skF_4',B_453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_7272])).

tff(c_7294,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7254,c_5890])).

tff(c_7358,plain,(
    ! [A_18] :
      ( r1_tarski('#skF_4',A_18)
      | ~ v5_relat_1('#skF_4',A_18)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7294,c_26])).

tff(c_7380,plain,(
    ! [A_18] : r1_tarski('#skF_4',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_7289,c_7358])).

tff(c_6527,plain,(
    ! [A_525,B_526,C_527,D_528] :
      ( k8_relset_1(A_525,B_526,C_527,D_528) = k10_relat_1(C_527,D_528)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7513,plain,(
    ! [A_596,B_597,A_598,D_599] :
      ( k8_relset_1(A_596,B_597,A_598,D_599) = k10_relat_1(A_598,D_599)
      | ~ r1_tarski(A_598,k2_zfmisc_1(A_596,B_597)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6527])).

tff(c_7516,plain,(
    ! [A_596,B_597,D_599] : k8_relset_1(A_596,B_597,'#skF_4',D_599) = k10_relat_1('#skF_4',D_599) ),
    inference(resolution,[status(thm)],[c_7380,c_7513])).

tff(c_7533,plain,(
    ! [A_596,B_597,D_599] : k8_relset_1(A_596,B_597,'#skF_4',D_599) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7478,c_7516])).

tff(c_5864,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_68])).

tff(c_5950,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5949,c_5864])).

tff(c_5995,plain,(
    ! [A_440,B_441] :
      ( r1_tarski(A_440,B_441)
      | ~ m1_subset_1(A_440,k1_zfmisc_1(B_441)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5999,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5950,c_5995])).

tff(c_6577,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5999,c_6565])).

tff(c_6583,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5865,c_6577])).

tff(c_6613,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6583,c_5890])).

tff(c_5906,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_5859,c_64])).

tff(c_6620,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6613,c_5906])).

tff(c_7546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7533,c_6620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.74  
% 7.02/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.02/2.74  
% 7.02/2.74  %Foreground sorts:
% 7.02/2.74  
% 7.02/2.74  
% 7.02/2.74  %Background operators:
% 7.02/2.74  
% 7.02/2.74  
% 7.02/2.74  %Foreground operators:
% 7.02/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.02/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.02/2.74  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.02/2.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.02/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.02/2.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.02/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.02/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.02/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.02/2.74  tff('#skF_3', type, '#skF_3': $i).
% 7.02/2.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.02/2.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.02/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.02/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.02/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.02/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.02/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.02/2.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.02/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.02/2.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.02/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.02/2.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.02/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.02/2.74  
% 7.02/2.76  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 7.02/2.76  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.02/2.76  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.02/2.76  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.02/2.76  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.02/2.76  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.02/2.76  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.02/2.76  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.02/2.76  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 7.02/2.76  tff(f_91, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.02/2.76  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.02/2.76  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 7.02/2.76  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.02/2.76  tff(f_47, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 7.02/2.76  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.02/2.76  tff(f_68, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 7.02/2.76  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.02/2.76  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.02/2.76  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.02/2.76  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.02/2.76  tff(c_847, plain, (![A_161, B_162, C_163, D_164]: (k8_relset_1(A_161, B_162, C_163, D_164)=k10_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.02/2.76  tff(c_860, plain, (![D_164]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_164)=k10_relat_1('#skF_5', D_164))), inference(resolution, [status(thm)], [c_68, c_847])).
% 7.02/2.76  tff(c_64, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.02/2.76  tff(c_861, plain, (k10_relat_1('#skF_5', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_860, c_64])).
% 7.02/2.76  tff(c_30, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.02/2.76  tff(c_279, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.02/2.76  tff(c_285, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_279])).
% 7.02/2.76  tff(c_289, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_285])).
% 7.02/2.76  tff(c_66, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.02/2.76  tff(c_75, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 7.02/2.76  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.02/2.76  tff(c_750, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.02/2.76  tff(c_768, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_750])).
% 7.02/2.76  tff(c_1290, plain, (![B_194, A_195, C_196]: (k1_xboole_0=B_194 | k1_relset_1(A_195, B_194, C_196)=A_195 | ~v1_funct_2(C_196, A_195, B_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.02/2.76  tff(c_1306, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_1290])).
% 7.02/2.76  tff(c_1311, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_768, c_1306])).
% 7.02/2.76  tff(c_1312, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_75, c_1311])).
% 7.02/2.76  tff(c_484, plain, (![C_110, B_111, A_112]: (v5_relat_1(C_110, B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.02/2.76  tff(c_502, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_484])).
% 7.02/2.76  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.02/2.76  tff(c_598, plain, (![B_130, A_131]: (k5_relat_1(B_130, k6_relat_1(A_131))=B_130 | ~r1_tarski(k2_relat_1(B_130), A_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.02/2.76  tff(c_990, plain, (![B_177, A_178]: (k5_relat_1(B_177, k6_relat_1(A_178))=B_177 | ~v5_relat_1(B_177, A_178) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_26, c_598])).
% 7.02/2.76  tff(c_40, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.02/2.76  tff(c_34, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.02/2.76  tff(c_684, plain, (![A_140, B_141]: (k10_relat_1(A_140, k1_relat_1(B_141))=k1_relat_1(k5_relat_1(A_140, B_141)) | ~v1_relat_1(B_141) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.02/2.76  tff(c_702, plain, (![A_140, A_26]: (k1_relat_1(k5_relat_1(A_140, k6_relat_1(A_26)))=k10_relat_1(A_140, A_26) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_34, c_684])).
% 7.02/2.76  tff(c_710, plain, (![A_140, A_26]: (k1_relat_1(k5_relat_1(A_140, k6_relat_1(A_26)))=k10_relat_1(A_140, A_26) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_702])).
% 7.02/2.76  tff(c_5748, plain, (![B_420, A_421]: (k10_relat_1(B_420, A_421)=k1_relat_1(B_420) | ~v1_relat_1(B_420) | ~v5_relat_1(B_420, A_421) | ~v1_relat_1(B_420))), inference(superposition, [status(thm), theory('equality')], [c_990, c_710])).
% 7.02/2.76  tff(c_5808, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_502, c_5748])).
% 7.02/2.76  tff(c_5849, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_1312, c_5808])).
% 7.02/2.76  tff(c_5851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_861, c_5849])).
% 7.02/2.76  tff(c_5853, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 7.02/2.76  tff(c_5852, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 7.02/2.76  tff(c_5859, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5853, c_5852])).
% 7.02/2.76  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.02/2.76  tff(c_5854, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5852, c_12])).
% 7.02/2.76  tff(c_5865, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_5854])).
% 7.02/2.76  tff(c_5931, plain, (![A_433, B_434]: (v1_xboole_0(k2_zfmisc_1(A_433, B_434)) | ~v1_xboole_0(B_434))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.02/2.76  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.76  tff(c_5890, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_5853, c_14])).
% 7.02/2.76  tff(c_5940, plain, (![A_435, B_436]: (k2_zfmisc_1(A_435, B_436)='#skF_4' | ~v1_xboole_0(B_436))), inference(resolution, [status(thm)], [c_5931, c_5890])).
% 7.02/2.76  tff(c_5951, plain, (![A_437]: (k2_zfmisc_1(A_437, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_5865, c_5940])).
% 7.02/2.76  tff(c_5958, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5951, c_30])).
% 7.02/2.76  tff(c_5898, plain, (![A_429]: (v1_xboole_0(k1_relat_1(A_429)) | ~v1_xboole_0(A_429))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.02/2.76  tff(c_5907, plain, (![A_430]: (k1_relat_1(A_430)='#skF_4' | ~v1_xboole_0(A_430))), inference(resolution, [status(thm)], [c_5898, c_5890])).
% 7.02/2.76  tff(c_5915, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5865, c_5907])).
% 7.02/2.76  tff(c_5949, plain, (![A_435]: (k2_zfmisc_1(A_435, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_5865, c_5940])).
% 7.02/2.76  tff(c_6065, plain, (![A_452, B_453]: (r2_hidden('#skF_2'(A_452, B_453), A_452) | r1_tarski(A_452, B_453))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.02/2.76  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.02/2.76  tff(c_6073, plain, (![A_452]: (r1_tarski(A_452, A_452))), inference(resolution, [status(thm)], [c_6065, c_8])).
% 7.02/2.76  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.02/2.76  tff(c_6198, plain, (![C_481, B_482, A_483]: (v5_relat_1(C_481, B_482) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_483, B_482))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.02/2.76  tff(c_6315, plain, (![A_502, B_503, A_504]: (v5_relat_1(A_502, B_503) | ~r1_tarski(A_502, k2_zfmisc_1(A_504, B_503)))), inference(resolution, [status(thm)], [c_20, c_6198])).
% 7.02/2.76  tff(c_6370, plain, (![A_509, B_510]: (v5_relat_1(k2_zfmisc_1(A_509, B_510), B_510))), inference(resolution, [status(thm)], [c_6073, c_6315])).
% 7.02/2.76  tff(c_6376, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5949, c_6370])).
% 7.02/2.76  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.02/2.76  tff(c_6103, plain, (![C_461, B_462, A_463]: (r2_hidden(C_461, B_462) | ~r2_hidden(C_461, A_463) | ~r1_tarski(A_463, B_462))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.02/2.76  tff(c_6557, plain, (![A_534, B_535]: (r2_hidden('#skF_1'(A_534), B_535) | ~r1_tarski(A_534, B_535) | v1_xboole_0(A_534))), inference(resolution, [status(thm)], [c_4, c_6103])).
% 7.02/2.76  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.02/2.76  tff(c_6565, plain, (![B_536, A_537]: (~v1_xboole_0(B_536) | ~r1_tarski(A_537, B_536) | v1_xboole_0(A_537))), inference(resolution, [status(thm)], [c_6557, c_2])).
% 7.02/2.76  tff(c_7219, plain, (![A_585, B_586]: (~v1_xboole_0(A_585) | v1_xboole_0(k2_relat_1(B_586)) | ~v5_relat_1(B_586, A_585) | ~v1_relat_1(B_586))), inference(resolution, [status(thm)], [c_26, c_6565])).
% 7.02/2.76  tff(c_7229, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6376, c_7219])).
% 7.02/2.76  tff(c_7254, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_5865, c_7229])).
% 7.02/2.76  tff(c_6074, plain, (![A_452, B_453]: (~v1_xboole_0(A_452) | r1_tarski(A_452, B_453))), inference(resolution, [status(thm)], [c_6065, c_2])).
% 7.02/2.76  tff(c_6267, plain, (![B_496, A_497]: (k5_relat_1(B_496, k6_relat_1(A_497))=B_496 | ~r1_tarski(k2_relat_1(B_496), A_497) | ~v1_relat_1(B_496))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.02/2.76  tff(c_6283, plain, (![B_496, B_453]: (k5_relat_1(B_496, k6_relat_1(B_453))=B_496 | ~v1_relat_1(B_496) | ~v1_xboole_0(k2_relat_1(B_496)))), inference(resolution, [status(thm)], [c_6074, c_6267])).
% 7.02/2.76  tff(c_7270, plain, (![B_453]: (k5_relat_1('#skF_4', k6_relat_1(B_453))='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7254, c_6283])).
% 7.02/2.76  tff(c_7453, plain, (![B_594]: (k5_relat_1('#skF_4', k6_relat_1(B_594))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_7270])).
% 7.02/2.76  tff(c_6343, plain, (![A_507, B_508]: (k10_relat_1(A_507, k1_relat_1(B_508))=k1_relat_1(k5_relat_1(A_507, B_508)) | ~v1_relat_1(B_508) | ~v1_relat_1(A_507))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.02/2.76  tff(c_6361, plain, (![A_507, A_26]: (k1_relat_1(k5_relat_1(A_507, k6_relat_1(A_26)))=k10_relat_1(A_507, A_26) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(A_507))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6343])).
% 7.02/2.76  tff(c_6369, plain, (![A_507, A_26]: (k1_relat_1(k5_relat_1(A_507, k6_relat_1(A_26)))=k10_relat_1(A_507, A_26) | ~v1_relat_1(A_507))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6361])).
% 7.02/2.76  tff(c_7458, plain, (![B_594]: (k10_relat_1('#skF_4', B_594)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7453, c_6369])).
% 7.02/2.76  tff(c_7478, plain, (![B_594]: (k10_relat_1('#skF_4', B_594)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_5915, c_7458])).
% 7.02/2.76  tff(c_6134, plain, (![B_465, A_466]: (v5_relat_1(B_465, A_466) | ~r1_tarski(k2_relat_1(B_465), A_466) | ~v1_relat_1(B_465))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.02/2.76  tff(c_6146, plain, (![B_465, B_453]: (v5_relat_1(B_465, B_453) | ~v1_relat_1(B_465) | ~v1_xboole_0(k2_relat_1(B_465)))), inference(resolution, [status(thm)], [c_6074, c_6134])).
% 7.02/2.76  tff(c_7272, plain, (![B_453]: (v5_relat_1('#skF_4', B_453) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7254, c_6146])).
% 7.02/2.76  tff(c_7289, plain, (![B_453]: (v5_relat_1('#skF_4', B_453))), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_7272])).
% 7.02/2.76  tff(c_7294, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_7254, c_5890])).
% 7.02/2.76  tff(c_7358, plain, (![A_18]: (r1_tarski('#skF_4', A_18) | ~v5_relat_1('#skF_4', A_18) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7294, c_26])).
% 7.02/2.76  tff(c_7380, plain, (![A_18]: (r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_7289, c_7358])).
% 7.02/2.76  tff(c_6527, plain, (![A_525, B_526, C_527, D_528]: (k8_relset_1(A_525, B_526, C_527, D_528)=k10_relat_1(C_527, D_528) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.02/2.76  tff(c_7513, plain, (![A_596, B_597, A_598, D_599]: (k8_relset_1(A_596, B_597, A_598, D_599)=k10_relat_1(A_598, D_599) | ~r1_tarski(A_598, k2_zfmisc_1(A_596, B_597)))), inference(resolution, [status(thm)], [c_20, c_6527])).
% 7.02/2.76  tff(c_7516, plain, (![A_596, B_597, D_599]: (k8_relset_1(A_596, B_597, '#skF_4', D_599)=k10_relat_1('#skF_4', D_599))), inference(resolution, [status(thm)], [c_7380, c_7513])).
% 7.02/2.76  tff(c_7533, plain, (![A_596, B_597, D_599]: (k8_relset_1(A_596, B_597, '#skF_4', D_599)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7478, c_7516])).
% 7.02/2.76  tff(c_5864, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_68])).
% 7.02/2.76  tff(c_5950, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5949, c_5864])).
% 7.02/2.76  tff(c_5995, plain, (![A_440, B_441]: (r1_tarski(A_440, B_441) | ~m1_subset_1(A_440, k1_zfmisc_1(B_441)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.02/2.76  tff(c_5999, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5950, c_5995])).
% 7.02/2.76  tff(c_6577, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5999, c_6565])).
% 7.02/2.76  tff(c_6583, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5865, c_6577])).
% 7.02/2.76  tff(c_6613, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6583, c_5890])).
% 7.02/2.76  tff(c_5906, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_5859, c_64])).
% 7.02/2.76  tff(c_6620, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6613, c_5906])).
% 7.02/2.76  tff(c_7546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7533, c_6620])).
% 7.02/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.76  
% 7.02/2.76  Inference rules
% 7.02/2.76  ----------------------
% 7.02/2.76  #Ref     : 0
% 7.02/2.76  #Sup     : 1649
% 7.02/2.76  #Fact    : 0
% 7.02/2.76  #Define  : 0
% 7.02/2.76  #Split   : 13
% 7.02/2.76  #Chain   : 0
% 7.02/2.76  #Close   : 0
% 7.02/2.76  
% 7.02/2.76  Ordering : KBO
% 7.02/2.76  
% 7.02/2.76  Simplification rules
% 7.02/2.76  ----------------------
% 7.02/2.76  #Subsume      : 415
% 7.02/2.76  #Demod        : 1377
% 7.02/2.76  #Tautology    : 803
% 7.02/2.76  #SimpNegUnit  : 74
% 7.02/2.76  #BackRed      : 60
% 7.02/2.76  
% 7.02/2.76  #Partial instantiations: 0
% 7.02/2.76  #Strategies tried      : 1
% 7.02/2.76  
% 7.02/2.76  Timing (in seconds)
% 7.02/2.76  ----------------------
% 7.02/2.76  Preprocessing        : 0.56
% 7.02/2.76  Parsing              : 0.29
% 7.02/2.76  CNF conversion       : 0.04
% 7.02/2.76  Main loop            : 1.34
% 7.02/2.76  Inferencing          : 0.45
% 7.02/2.76  Reduction            : 0.43
% 7.02/2.76  Demodulation         : 0.30
% 7.02/2.77  BG Simplification    : 0.06
% 7.02/2.77  Subsumption          : 0.29
% 7.02/2.77  Abstraction          : 0.05
% 7.02/2.77  MUC search           : 0.00
% 7.02/2.77  Cooper               : 0.00
% 7.02/2.77  Total                : 1.95
% 7.02/2.77  Index Insertion      : 0.00
% 7.02/2.77  Index Deletion       : 0.00
% 7.02/2.77  Index Matching       : 0.00
% 7.02/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
