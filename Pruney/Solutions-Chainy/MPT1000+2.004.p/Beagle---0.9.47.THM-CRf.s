%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 487 expanded)
%              Number of leaves         :   47 ( 168 expanded)
%              Depth                    :   18
%              Number of atoms          :  214 (1108 expanded)
%              Number of equality atoms :   75 ( 582 expanded)
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

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_74,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_774,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k8_relset_1(A_169,B_170,C_171,D_172) = k10_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_785,plain,(
    ! [D_172] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_172) = k10_relat_1('#skF_5',D_172) ),
    inference(resolution,[status(thm)],[c_76,c_774])).

tff(c_72,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_803,plain,(
    k10_relat_1('#skF_5','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_72])).

tff(c_42,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_263,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_263])).

tff(c_273,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_269])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_583,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_598,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_583])).

tff(c_898,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_905,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_898])).

tff(c_915,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_598,c_905])).

tff(c_916,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_915])).

tff(c_389,plain,(
    ! [C_102,B_103,A_104] :
      ( v5_relat_1(C_102,B_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_404,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_389])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_514,plain,(
    ! [B_129,A_130] :
      ( k5_relat_1(B_129,k6_relat_1(A_130)) = B_129
      | ~ r1_tarski(k2_relat_1(B_129),A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_983,plain,(
    ! [B_192,A_193] :
      ( k5_relat_1(B_192,k6_relat_1(A_193)) = B_192
      | ~ v5_relat_1(B_192,A_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_36,c_514])).

tff(c_38,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_660,plain,(
    ! [A_151,B_152] :
      ( k10_relat_1(A_151,k1_relat_1(B_152)) = k1_relat_1(k5_relat_1(A_151,B_152))
      | ~ v1_relat_1(B_152)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_675,plain,(
    ! [A_151,A_29] :
      ( k1_relat_1(k5_relat_1(A_151,k6_relat_1(A_29))) = k10_relat_1(A_151,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_660])).

tff(c_681,plain,(
    ! [A_151,A_29] :
      ( k1_relat_1(k5_relat_1(A_151,k6_relat_1(A_29))) = k10_relat_1(A_151,A_29)
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_675])).

tff(c_5656,plain,(
    ! [B_459,A_460] :
      ( k10_relat_1(B_459,A_460) = k1_relat_1(B_459)
      | ~ v1_relat_1(B_459)
      | ~ v5_relat_1(B_459,A_460)
      | ~ v1_relat_1(B_459) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_681])).

tff(c_5707,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_404,c_5656])).

tff(c_5745,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_916,c_5707])).

tff(c_5747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_803,c_5745])).

tff(c_5749,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_24,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5793,plain,(
    ! [A_466] : k2_zfmisc_1(A_466,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_5749,c_24])).

tff(c_5797,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5793,c_42])).

tff(c_5748,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5755,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_5748])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5750,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5748,c_12])).

tff(c_5761,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5755,c_5750])).

tff(c_5822,plain,(
    ! [A_468] :
      ( v1_xboole_0(k1_relat_1(A_468))
      | ~ v1_xboole_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5784,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_14])).

tff(c_5831,plain,(
    ! [A_471] :
      ( k1_relat_1(A_471) = '#skF_4'
      | ~ v1_xboole_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_5822,c_5784])).

tff(c_5839,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5761,c_5831])).

tff(c_5908,plain,(
    ! [A_482,B_483] :
      ( r2_hidden('#skF_2'(A_482,B_483),A_482)
      | r1_tarski(A_482,B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5912,plain,(
    ! [A_482,B_483] :
      ( ~ v1_xboole_0(A_482)
      | r1_tarski(A_482,B_483) ) ),
    inference(resolution,[status(thm)],[c_5908,c_2])).

tff(c_5792,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_5749,c_24])).

tff(c_5849,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5792,c_5755,c_76])).

tff(c_5885,plain,(
    ! [A_475,B_476] :
      ( r1_tarski(A_475,B_476)
      | ~ m1_subset_1(A_475,k1_zfmisc_1(B_476)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5889,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5849,c_5885])).

tff(c_5932,plain,(
    ! [B_490,A_491] :
      ( B_490 = A_491
      | ~ r1_tarski(B_490,A_491)
      | ~ r1_tarski(A_491,B_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5940,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_5889,c_5932])).

tff(c_5945,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5940])).

tff(c_5948,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5912,c_5945])).

tff(c_5952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5761,c_5948])).

tff(c_5953,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5940])).

tff(c_5957,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5953,c_5849])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5803,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_4',B_14) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_5749,c_26])).

tff(c_5991,plain,(
    ! [C_495,B_496,A_497] :
      ( v5_relat_1(C_495,B_496)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_497,B_496))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6114,plain,(
    ! [C_518,B_519] :
      ( v5_relat_1(C_518,B_519)
      | ~ m1_subset_1(C_518,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5803,c_5991])).

tff(c_6120,plain,(
    ! [B_519] : v5_relat_1('#skF_4',B_519) ),
    inference(resolution,[status(thm)],[c_5957,c_6114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6067,plain,(
    ! [C_507,B_508,A_509] :
      ( r2_hidden(C_507,B_508)
      | ~ r2_hidden(C_507,A_509)
      | ~ r1_tarski(A_509,B_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6373,plain,(
    ! [A_572,B_573] :
      ( r2_hidden('#skF_1'(A_572),B_573)
      | ~ r1_tarski(A_572,B_573)
      | v1_xboole_0(A_572) ) ),
    inference(resolution,[status(thm)],[c_4,c_6067])).

tff(c_6381,plain,(
    ! [B_574,A_575] :
      ( ~ v1_xboole_0(B_574)
      | ~ r1_tarski(A_575,B_574)
      | v1_xboole_0(A_575) ) ),
    inference(resolution,[status(thm)],[c_6373,c_2])).

tff(c_6920,plain,(
    ! [A_627,B_628] :
      ( ~ v1_xboole_0(A_627)
      | v1_xboole_0(k2_relat_1(B_628))
      | ~ v5_relat_1(B_628,A_627)
      | ~ v1_relat_1(B_628) ) ),
    inference(resolution,[status(thm)],[c_36,c_6381])).

tff(c_6930,plain,(
    ! [B_519] :
      ( ~ v1_xboole_0(B_519)
      | v1_xboole_0(k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6120,c_6920])).

tff(c_6947,plain,(
    ! [B_519] :
      ( ~ v1_xboole_0(B_519)
      | v1_xboole_0(k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_6930])).

tff(c_6955,plain,(
    ! [B_519] : ~ v1_xboole_0(B_519) ),
    inference(splitLeft,[status(thm)],[c_6947])).

tff(c_6963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6955,c_5761])).

tff(c_6964,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6947])).

tff(c_6187,plain,(
    ! [B_537,A_538] :
      ( k5_relat_1(B_537,k6_relat_1(A_538)) = B_537
      | ~ r1_tarski(k2_relat_1(B_537),A_538)
      | ~ v1_relat_1(B_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6203,plain,(
    ! [B_537,B_483] :
      ( k5_relat_1(B_537,k6_relat_1(B_483)) = B_537
      | ~ v1_relat_1(B_537)
      | ~ v1_xboole_0(k2_relat_1(B_537)) ) ),
    inference(resolution,[status(thm)],[c_5912,c_6187])).

tff(c_6966,plain,(
    ! [B_483] :
      ( k5_relat_1('#skF_4',k6_relat_1(B_483)) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6964,c_6203])).

tff(c_7101,plain,(
    ! [B_633] : k5_relat_1('#skF_4',k6_relat_1(B_633)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_6966])).

tff(c_6298,plain,(
    ! [A_559,B_560] :
      ( k10_relat_1(A_559,k1_relat_1(B_560)) = k1_relat_1(k5_relat_1(A_559,B_560))
      | ~ v1_relat_1(B_560)
      | ~ v1_relat_1(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6313,plain,(
    ! [A_559,A_29] :
      ( k1_relat_1(k5_relat_1(A_559,k6_relat_1(A_29))) = k10_relat_1(A_559,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_559) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6298])).

tff(c_6319,plain,(
    ! [A_559,A_29] :
      ( k1_relat_1(k5_relat_1(A_559,k6_relat_1(A_29))) = k10_relat_1(A_559,A_29)
      | ~ v1_relat_1(A_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6313])).

tff(c_7106,plain,(
    ! [B_633] :
      ( k10_relat_1('#skF_4',B_633) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7101,c_6319])).

tff(c_7126,plain,(
    ! [B_633] : k10_relat_1('#skF_4',B_633) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_5839,c_7106])).

tff(c_6415,plain,(
    ! [A_577,B_578,C_579,D_580] :
      ( k8_relset_1(A_577,B_578,C_579,D_580) = k10_relat_1(C_579,D_580)
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_577,B_578))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7822,plain,(
    ! [A_679,C_680,D_681] :
      ( k8_relset_1(A_679,'#skF_4',C_680,D_681) = k10_relat_1(C_680,D_681)
      | ~ m1_subset_1(C_680,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5792,c_6415])).

tff(c_7824,plain,(
    ! [A_679,D_681] : k8_relset_1(A_679,'#skF_4','#skF_4',D_681) = k10_relat_1('#skF_4',D_681) ),
    inference(resolution,[status(thm)],[c_5957,c_7822])).

tff(c_7829,plain,(
    ! [A_679,D_681] : k8_relset_1(A_679,'#skF_4','#skF_4',D_681) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7126,c_7824])).

tff(c_5802,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5755,c_5755,c_72])).

tff(c_5958,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5953,c_5802])).

tff(c_7833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7829,c_5958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.50  
% 7.23/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.23/2.50  
% 7.23/2.50  %Foreground sorts:
% 7.23/2.50  
% 7.23/2.50  
% 7.23/2.50  %Background operators:
% 7.23/2.50  
% 7.23/2.50  
% 7.23/2.50  %Foreground operators:
% 7.23/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.23/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.23/2.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.23/2.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.23/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.23/2.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.23/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.23/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.23/2.50  tff('#skF_5', type, '#skF_5': $i).
% 7.23/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.23/2.50  tff('#skF_3', type, '#skF_3': $i).
% 7.23/2.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.23/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.23/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.23/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.23/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.23/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.23/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.23/2.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.23/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.23/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.23/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.23/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.23/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.23/2.50  
% 7.23/2.52  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 7.23/2.52  tff(f_111, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.23/2.52  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.23/2.52  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.23/2.52  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.23/2.52  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.23/2.52  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.23/2.52  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.23/2.52  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 7.23/2.52  tff(f_74, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.23/2.52  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.23/2.52  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 7.23/2.52  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.23/2.52  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.23/2.52  tff(f_78, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 7.23/2.52  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.23/2.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.23/2.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.23/2.52  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.23/2.52  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.23/2.52  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.23/2.52  tff(c_774, plain, (![A_169, B_170, C_171, D_172]: (k8_relset_1(A_169, B_170, C_171, D_172)=k10_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.23/2.52  tff(c_785, plain, (![D_172]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_172)=k10_relat_1('#skF_5', D_172))), inference(resolution, [status(thm)], [c_76, c_774])).
% 7.23/2.52  tff(c_72, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.23/2.52  tff(c_803, plain, (k10_relat_1('#skF_5', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_785, c_72])).
% 7.23/2.52  tff(c_42, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.23/2.52  tff(c_263, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.23/2.52  tff(c_269, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_263])).
% 7.23/2.52  tff(c_273, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_269])).
% 7.23/2.52  tff(c_74, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.23/2.52  tff(c_88, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_74])).
% 7.23/2.52  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.23/2.52  tff(c_583, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.23/2.52  tff(c_598, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_583])).
% 7.23/2.52  tff(c_898, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.23/2.52  tff(c_905, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_898])).
% 7.23/2.52  tff(c_915, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_598, c_905])).
% 7.23/2.52  tff(c_916, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_88, c_915])).
% 7.23/2.52  tff(c_389, plain, (![C_102, B_103, A_104]: (v5_relat_1(C_102, B_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.23/2.52  tff(c_404, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_389])).
% 7.23/2.52  tff(c_36, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.23/2.52  tff(c_514, plain, (![B_129, A_130]: (k5_relat_1(B_129, k6_relat_1(A_130))=B_129 | ~r1_tarski(k2_relat_1(B_129), A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.23/2.52  tff(c_983, plain, (![B_192, A_193]: (k5_relat_1(B_192, k6_relat_1(A_193))=B_192 | ~v5_relat_1(B_192, A_193) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_36, c_514])).
% 7.23/2.52  tff(c_38, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.23/2.52  tff(c_46, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.23/2.52  tff(c_660, plain, (![A_151, B_152]: (k10_relat_1(A_151, k1_relat_1(B_152))=k1_relat_1(k5_relat_1(A_151, B_152)) | ~v1_relat_1(B_152) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.23/2.52  tff(c_675, plain, (![A_151, A_29]: (k1_relat_1(k5_relat_1(A_151, k6_relat_1(A_29)))=k10_relat_1(A_151, A_29) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_46, c_660])).
% 7.23/2.52  tff(c_681, plain, (![A_151, A_29]: (k1_relat_1(k5_relat_1(A_151, k6_relat_1(A_29)))=k10_relat_1(A_151, A_29) | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_675])).
% 7.23/2.52  tff(c_5656, plain, (![B_459, A_460]: (k10_relat_1(B_459, A_460)=k1_relat_1(B_459) | ~v1_relat_1(B_459) | ~v5_relat_1(B_459, A_460) | ~v1_relat_1(B_459))), inference(superposition, [status(thm), theory('equality')], [c_983, c_681])).
% 7.23/2.52  tff(c_5707, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_404, c_5656])).
% 7.23/2.52  tff(c_5745, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_916, c_5707])).
% 7.23/2.52  tff(c_5747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_803, c_5745])).
% 7.23/2.52  tff(c_5749, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_74])).
% 7.23/2.52  tff(c_24, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.23/2.52  tff(c_5793, plain, (![A_466]: (k2_zfmisc_1(A_466, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_5749, c_24])).
% 7.23/2.52  tff(c_5797, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5793, c_42])).
% 7.23/2.52  tff(c_5748, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 7.23/2.52  tff(c_5755, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_5748])).
% 7.23/2.52  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.23/2.52  tff(c_5750, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5748, c_12])).
% 7.23/2.52  tff(c_5761, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5755, c_5750])).
% 7.23/2.52  tff(c_5822, plain, (![A_468]: (v1_xboole_0(k1_relat_1(A_468)) | ~v1_xboole_0(A_468))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.23/2.52  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.23/2.52  tff(c_5784, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_14])).
% 7.23/2.52  tff(c_5831, plain, (![A_471]: (k1_relat_1(A_471)='#skF_4' | ~v1_xboole_0(A_471))), inference(resolution, [status(thm)], [c_5822, c_5784])).
% 7.23/2.52  tff(c_5839, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5761, c_5831])).
% 7.23/2.52  tff(c_5908, plain, (![A_482, B_483]: (r2_hidden('#skF_2'(A_482, B_483), A_482) | r1_tarski(A_482, B_483))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.23/2.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.23/2.52  tff(c_5912, plain, (![A_482, B_483]: (~v1_xboole_0(A_482) | r1_tarski(A_482, B_483))), inference(resolution, [status(thm)], [c_5908, c_2])).
% 7.23/2.52  tff(c_5792, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_5749, c_24])).
% 7.23/2.52  tff(c_5849, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5792, c_5755, c_76])).
% 7.23/2.52  tff(c_5885, plain, (![A_475, B_476]: (r1_tarski(A_475, B_476) | ~m1_subset_1(A_475, k1_zfmisc_1(B_476)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.23/2.52  tff(c_5889, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5849, c_5885])).
% 7.23/2.52  tff(c_5932, plain, (![B_490, A_491]: (B_490=A_491 | ~r1_tarski(B_490, A_491) | ~r1_tarski(A_491, B_490))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.23/2.52  tff(c_5940, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_5889, c_5932])).
% 7.23/2.52  tff(c_5945, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_5940])).
% 7.23/2.52  tff(c_5948, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5912, c_5945])).
% 7.23/2.52  tff(c_5952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5761, c_5948])).
% 7.23/2.52  tff(c_5953, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5940])).
% 7.23/2.52  tff(c_5957, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5953, c_5849])).
% 7.23/2.52  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.23/2.52  tff(c_5803, plain, (![B_14]: (k2_zfmisc_1('#skF_4', B_14)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_5749, c_26])).
% 7.23/2.52  tff(c_5991, plain, (![C_495, B_496, A_497]: (v5_relat_1(C_495, B_496) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.23/2.52  tff(c_6114, plain, (![C_518, B_519]: (v5_relat_1(C_518, B_519) | ~m1_subset_1(C_518, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5803, c_5991])).
% 7.23/2.52  tff(c_6120, plain, (![B_519]: (v5_relat_1('#skF_4', B_519))), inference(resolution, [status(thm)], [c_5957, c_6114])).
% 7.23/2.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.23/2.52  tff(c_6067, plain, (![C_507, B_508, A_509]: (r2_hidden(C_507, B_508) | ~r2_hidden(C_507, A_509) | ~r1_tarski(A_509, B_508))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.23/2.52  tff(c_6373, plain, (![A_572, B_573]: (r2_hidden('#skF_1'(A_572), B_573) | ~r1_tarski(A_572, B_573) | v1_xboole_0(A_572))), inference(resolution, [status(thm)], [c_4, c_6067])).
% 7.23/2.52  tff(c_6381, plain, (![B_574, A_575]: (~v1_xboole_0(B_574) | ~r1_tarski(A_575, B_574) | v1_xboole_0(A_575))), inference(resolution, [status(thm)], [c_6373, c_2])).
% 7.23/2.52  tff(c_6920, plain, (![A_627, B_628]: (~v1_xboole_0(A_627) | v1_xboole_0(k2_relat_1(B_628)) | ~v5_relat_1(B_628, A_627) | ~v1_relat_1(B_628))), inference(resolution, [status(thm)], [c_36, c_6381])).
% 7.23/2.52  tff(c_6930, plain, (![B_519]: (~v1_xboole_0(B_519) | v1_xboole_0(k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6120, c_6920])).
% 7.23/2.52  tff(c_6947, plain, (![B_519]: (~v1_xboole_0(B_519) | v1_xboole_0(k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_6930])).
% 7.23/2.52  tff(c_6955, plain, (![B_519]: (~v1_xboole_0(B_519))), inference(splitLeft, [status(thm)], [c_6947])).
% 7.23/2.52  tff(c_6963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6955, c_5761])).
% 7.23/2.52  tff(c_6964, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6947])).
% 7.23/2.52  tff(c_6187, plain, (![B_537, A_538]: (k5_relat_1(B_537, k6_relat_1(A_538))=B_537 | ~r1_tarski(k2_relat_1(B_537), A_538) | ~v1_relat_1(B_537))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.23/2.52  tff(c_6203, plain, (![B_537, B_483]: (k5_relat_1(B_537, k6_relat_1(B_483))=B_537 | ~v1_relat_1(B_537) | ~v1_xboole_0(k2_relat_1(B_537)))), inference(resolution, [status(thm)], [c_5912, c_6187])).
% 7.23/2.52  tff(c_6966, plain, (![B_483]: (k5_relat_1('#skF_4', k6_relat_1(B_483))='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6964, c_6203])).
% 7.23/2.52  tff(c_7101, plain, (![B_633]: (k5_relat_1('#skF_4', k6_relat_1(B_633))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_6966])).
% 7.23/2.52  tff(c_6298, plain, (![A_559, B_560]: (k10_relat_1(A_559, k1_relat_1(B_560))=k1_relat_1(k5_relat_1(A_559, B_560)) | ~v1_relat_1(B_560) | ~v1_relat_1(A_559))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.23/2.52  tff(c_6313, plain, (![A_559, A_29]: (k1_relat_1(k5_relat_1(A_559, k6_relat_1(A_29)))=k10_relat_1(A_559, A_29) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_559))), inference(superposition, [status(thm), theory('equality')], [c_46, c_6298])).
% 7.23/2.52  tff(c_6319, plain, (![A_559, A_29]: (k1_relat_1(k5_relat_1(A_559, k6_relat_1(A_29)))=k10_relat_1(A_559, A_29) | ~v1_relat_1(A_559))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6313])).
% 7.23/2.52  tff(c_7106, plain, (![B_633]: (k10_relat_1('#skF_4', B_633)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7101, c_6319])).
% 7.23/2.52  tff(c_7126, plain, (![B_633]: (k10_relat_1('#skF_4', B_633)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_5839, c_7106])).
% 7.23/2.52  tff(c_6415, plain, (![A_577, B_578, C_579, D_580]: (k8_relset_1(A_577, B_578, C_579, D_580)=k10_relat_1(C_579, D_580) | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_577, B_578))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.23/2.52  tff(c_7822, plain, (![A_679, C_680, D_681]: (k8_relset_1(A_679, '#skF_4', C_680, D_681)=k10_relat_1(C_680, D_681) | ~m1_subset_1(C_680, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5792, c_6415])).
% 7.23/2.52  tff(c_7824, plain, (![A_679, D_681]: (k8_relset_1(A_679, '#skF_4', '#skF_4', D_681)=k10_relat_1('#skF_4', D_681))), inference(resolution, [status(thm)], [c_5957, c_7822])).
% 7.23/2.52  tff(c_7829, plain, (![A_679, D_681]: (k8_relset_1(A_679, '#skF_4', '#skF_4', D_681)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7126, c_7824])).
% 7.23/2.52  tff(c_5802, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5755, c_5755, c_72])).
% 7.23/2.52  tff(c_5958, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5953, c_5802])).
% 7.23/2.52  tff(c_7833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7829, c_5958])).
% 7.23/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.52  
% 7.23/2.52  Inference rules
% 7.23/2.52  ----------------------
% 7.23/2.52  #Ref     : 0
% 7.23/2.52  #Sup     : 1686
% 7.23/2.52  #Fact    : 0
% 7.23/2.52  #Define  : 0
% 7.23/2.52  #Split   : 24
% 7.23/2.52  #Chain   : 0
% 7.23/2.52  #Close   : 0
% 7.23/2.52  
% 7.23/2.52  Ordering : KBO
% 7.23/2.52  
% 7.23/2.52  Simplification rules
% 7.23/2.52  ----------------------
% 7.23/2.52  #Subsume      : 689
% 7.23/2.52  #Demod        : 1332
% 7.23/2.52  #Tautology    : 710
% 7.23/2.52  #SimpNegUnit  : 131
% 7.23/2.52  #BackRed      : 80
% 7.23/2.52  
% 7.23/2.52  #Partial instantiations: 0
% 7.23/2.52  #Strategies tried      : 1
% 7.23/2.52  
% 7.23/2.52  Timing (in seconds)
% 7.23/2.52  ----------------------
% 7.23/2.53  Preprocessing        : 0.34
% 7.23/2.53  Parsing              : 0.18
% 7.23/2.53  CNF conversion       : 0.02
% 7.23/2.53  Main loop            : 1.41
% 7.23/2.53  Inferencing          : 0.46
% 7.23/2.53  Reduction            : 0.45
% 7.23/2.53  Demodulation         : 0.32
% 7.23/2.53  BG Simplification    : 0.05
% 7.23/2.53  Subsumption          : 0.33
% 7.23/2.53  Abstraction          : 0.06
% 7.23/2.53  MUC search           : 0.00
% 7.23/2.53  Cooper               : 0.00
% 7.23/2.53  Total                : 1.79
% 7.23/2.53  Index Insertion      : 0.00
% 7.23/2.53  Index Deletion       : 0.00
% 7.23/2.53  Index Matching       : 0.00
% 7.23/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
