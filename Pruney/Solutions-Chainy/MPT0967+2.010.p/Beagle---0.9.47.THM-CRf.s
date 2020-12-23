%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 13.58s
% Output     : CNFRefutation 13.97s
% Verified   : 
% Statistics : Number of formulae       :  371 (3123 expanded)
%              Number of leaves         :   40 ( 996 expanded)
%              Depth                    :   16
%              Number of atoms          :  635 (8541 expanded)
%              Number of equality atoms :  150 (2757 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_33319,plain,(
    ! [C_1511,A_1512,B_1513] :
      ( v1_relat_1(C_1511)
      | ~ m1_subset_1(C_1511,k1_zfmisc_1(k2_zfmisc_1(A_1512,B_1513))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_33332,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_33319])).

tff(c_33610,plain,(
    ! [C_1560,B_1561,A_1562] :
      ( v5_relat_1(C_1560,B_1561)
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(A_1562,B_1561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_33625,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_33610])).

tff(c_33672,plain,(
    ! [B_1576,A_1577] :
      ( r1_tarski(k2_relat_1(B_1576),A_1577)
      | ~ v5_relat_1(B_1576,A_1577)
      | ~ v1_relat_1(B_1576) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_33496,plain,(
    ! [A_1545,C_1546,B_1547] :
      ( r1_tarski(A_1545,C_1546)
      | ~ r1_tarski(B_1547,C_1546)
      | ~ r1_tarski(A_1545,B_1547) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33509,plain,(
    ! [A_1548] :
      ( r1_tarski(A_1548,'#skF_5')
      | ~ r1_tarski(A_1548,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_33496])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_33523,plain,(
    ! [B_21] :
      ( v5_relat_1(B_21,'#skF_5')
      | ~ v1_relat_1(B_21)
      | ~ r1_tarski(k2_relat_1(B_21),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_33509,c_34])).

tff(c_33712,plain,(
    ! [B_1576] :
      ( v5_relat_1(B_1576,'#skF_5')
      | ~ v5_relat_1(B_1576,'#skF_4')
      | ~ v1_relat_1(B_1576) ) ),
    inference(resolution,[status(thm)],[c_33672,c_33523])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35068,plain,(
    ! [D_1674,C_1675,B_1676,A_1677] :
      ( m1_subset_1(D_1674,k1_zfmisc_1(k2_zfmisc_1(C_1675,B_1676)))
      | ~ r1_tarski(k2_relat_1(D_1674),B_1676)
      | ~ m1_subset_1(D_1674,k1_zfmisc_1(k2_zfmisc_1(C_1675,A_1677))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_35092,plain,(
    ! [B_1678] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1678)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_1678) ) ),
    inference(resolution,[status(thm)],[c_68,c_35068])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6804,plain,(
    ! [A_412,B_413,C_414] :
      ( k1_relset_1(A_412,B_413,C_414) = k1_relat_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6819,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_6804])).

tff(c_7647,plain,(
    ! [A_463,B_464,C_465] :
      ( m1_subset_1(k1_relset_1(A_463,B_464,C_465),k1_zfmisc_1(A_463))
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7688,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6819,c_7647])).

tff(c_7707,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7688])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7711,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7707,c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6206,plain,(
    ! [C_374,B_375,A_376] :
      ( r2_hidden(C_374,B_375)
      | ~ r2_hidden(C_374,A_376)
      | ~ r1_tarski(A_376,B_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6667,plain,(
    ! [A_404,B_405] :
      ( r2_hidden('#skF_1'(A_404),B_405)
      | ~ r1_tarski(A_404,B_405)
      | v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_4,c_6206])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6674,plain,(
    ! [B_405,A_404] :
      ( ~ v1_xboole_0(B_405)
      | ~ r1_tarski(A_404,B_405)
      | v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_6667,c_2])).

tff(c_7732,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7711,c_6674])).

tff(c_7738,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7732])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8000,plain,(
    ! [B_476,A_477,C_478] :
      ( k1_xboole_0 = B_476
      | k1_relset_1(A_477,B_476,C_478) = A_477
      | ~ v1_funct_2(C_478,A_477,B_476)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_zfmisc_1(A_477,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8014,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8000])).

tff(c_8026,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6819,c_8014])).

tff(c_8027,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_8026])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7737,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7711,c_14])).

tff(c_7744,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7737])).

tff(c_8030,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_7744])).

tff(c_8036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8030])).

tff(c_8037,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7737])).

tff(c_26,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_154,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_203,plain,(
    ! [C_66] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_154])).

tff(c_209,plain,(
    ! [A_67] :
      ( v1_relat_1(A_67)
      | ~ r1_tarski(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_219,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_209])).

tff(c_326,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_365,plain,(
    ! [A_92,B_93,A_94] :
      ( v5_relat_1(A_92,B_93)
      | ~ r1_tarski(A_92,k2_zfmisc_1(A_94,B_93)) ) ),
    inference(resolution,[status(thm)],[c_32,c_326])).

tff(c_392,plain,(
    ! [A_97,B_98] : v5_relat_1(k2_zfmisc_1(A_97,B_98),B_98) ),
    inference(resolution,[status(thm)],[c_18,c_365])).

tff(c_395,plain,(
    ! [B_17] : v5_relat_1(k1_xboole_0,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_392])).

tff(c_253,plain,(
    ! [A_74,A_75,B_76] :
      ( v1_relat_1(A_74)
      | ~ r1_tarski(A_74,k2_zfmisc_1(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_276,plain,(
    ! [A_75,B_76] : v1_relat_1(k2_zfmisc_1(A_75,B_76)) ),
    inference(resolution,[status(thm)],[c_18,c_253])).

tff(c_390,plain,(
    ! [A_94,B_93] : v5_relat_1(k2_zfmisc_1(A_94,B_93),B_93) ),
    inference(resolution,[status(thm)],[c_18,c_365])).

tff(c_6292,plain,(
    ! [B_387,A_388] :
      ( r1_tarski(k2_relat_1(B_387),A_388)
      | ~ v5_relat_1(B_387,A_388)
      | ~ v1_relat_1(B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6393,plain,(
    ! [B_390] :
      ( k2_relat_1(B_390) = k1_xboole_0
      | ~ v5_relat_1(B_390,k1_xboole_0)
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_6292,c_22])).

tff(c_6401,plain,(
    ! [A_94] :
      ( k2_relat_1(k2_zfmisc_1(A_94,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_94,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_390,c_6393])).

tff(c_6415,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_26,c_6401])).

tff(c_6421,plain,(
    ! [A_20] :
      ( r1_tarski(k1_xboole_0,A_20)
      | ~ v5_relat_1(k1_xboole_0,A_20)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6415,c_36])).

tff(c_6436,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_395,c_6421])).

tff(c_167,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_154])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_342,plain,(
    ! [C_87,B_88] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_326])).

tff(c_346,plain,(
    ! [A_18,B_88] :
      ( v5_relat_1(A_18,B_88)
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_342])).

tff(c_6447,plain,(
    ! [A_391] : r1_tarski(k1_xboole_0,A_391) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_395,c_6421])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6544,plain,(
    ! [A_394,A_395] :
      ( r1_tarski(A_394,A_395)
      | ~ r1_tarski(A_394,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6447,c_20])).

tff(c_6559,plain,(
    ! [B_21,A_395] :
      ( r1_tarski(k2_relat_1(B_21),A_395)
      | ~ v5_relat_1(B_21,k1_xboole_0)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_36,c_6544])).

tff(c_8070,plain,(
    ! [D_481,C_482,B_483,A_484] :
      ( m1_subset_1(D_481,k1_zfmisc_1(k2_zfmisc_1(C_482,B_483)))
      | ~ r1_tarski(k2_relat_1(D_481),B_483)
      | ~ m1_subset_1(D_481,k1_zfmisc_1(k2_zfmisc_1(C_482,A_484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8108,plain,(
    ! [B_489] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_489)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_489) ) ),
    inference(resolution,[status(thm)],[c_68,c_8070])).

tff(c_40,plain,(
    ! [C_27,B_26,A_25] :
      ( v5_relat_1(C_27,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8139,plain,(
    ! [B_490] :
      ( v5_relat_1('#skF_6',B_490)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_490) ) ),
    inference(resolution,[status(thm)],[c_8108,c_40])).

tff(c_8151,plain,(
    ! [A_395] :
      ( v5_relat_1('#skF_6',A_395)
      | ~ v5_relat_1('#skF_6',k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6559,c_8139])).

tff(c_8184,plain,(
    ! [A_395] :
      ( v5_relat_1('#skF_6',A_395)
      | ~ v5_relat_1('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_8151])).

tff(c_8194,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8184])).

tff(c_8231,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_346,c_8194])).

tff(c_341,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_326])).

tff(c_220,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,'#skF_5')
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_220])).

tff(c_8190,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_8139])).

tff(c_8236,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8190])).

tff(c_8245,plain,
    ( ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_8236])).

tff(c_8258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_341,c_8245])).

tff(c_8260,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8190])).

tff(c_239,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,'#skF_5')
      | ~ r1_tarski(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_220])).

tff(c_244,plain,(
    ! [A_12,A_72] :
      ( r1_tarski(A_12,'#skF_5')
      | ~ r1_tarski(A_12,A_72)
      | ~ r1_tarski(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_239,c_20])).

tff(c_8280,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_8260,c_244])).

tff(c_8303,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8280])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_141,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_8605,plain,(
    ! [B_505] :
      ( r1_tarski('#skF_6',k2_zfmisc_1('#skF_3',B_505))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_505) ) ),
    inference(resolution,[status(thm)],[c_8108,c_30])).

tff(c_8639,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_8605])).

tff(c_8667,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8260,c_8639])).

tff(c_8763,plain,(
    ! [A_506,B_507,A_508] :
      ( k1_relset_1(A_506,B_507,A_508) = k1_relat_1(A_508)
      | ~ r1_tarski(A_508,k2_zfmisc_1(A_506,B_507)) ) ),
    inference(resolution,[status(thm)],[c_32,c_6804])).

tff(c_8769,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8667,c_8763])).

tff(c_8805,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8037,c_8769])).

tff(c_8085,plain,(
    ! [B_483] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_483)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_483) ) ),
    inference(resolution,[status(thm)],[c_68,c_8070])).

tff(c_8195,plain,(
    ! [B_491,C_492,A_493] :
      ( k1_xboole_0 = B_491
      | v1_funct_2(C_492,A_493,B_491)
      | k1_relset_1(A_493,B_491,C_492) != A_493
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_493,B_491))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9137,plain,(
    ! [B_521] :
      ( k1_xboole_0 = B_521
      | v1_funct_2('#skF_6','#skF_3',B_521)
      | k1_relset_1('#skF_3',B_521,'#skF_6') != '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_521) ) ),
    inference(resolution,[status(thm)],[c_8085,c_8195])).

tff(c_9175,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_3','#skF_5')
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_9137])).

tff(c_9214,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8260,c_8805,c_9175])).

tff(c_9215,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_9214])).

tff(c_8129,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8108])).

tff(c_8410,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8129])).

tff(c_9225,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9215,c_8410])).

tff(c_9269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8303,c_9225])).

tff(c_9270,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_8129])).

tff(c_9287,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9270,c_30])).

tff(c_9299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8231,c_9287])).

tff(c_9305,plain,(
    ! [A_522] : v5_relat_1('#skF_6',A_522) ),
    inference(splitRight,[status(thm)],[c_8184])).

tff(c_6352,plain,(
    ! [B_387] :
      ( k2_relat_1(B_387) = k1_xboole_0
      | ~ v5_relat_1(B_387,k1_xboole_0)
      | ~ v1_relat_1(B_387) ) ),
    inference(resolution,[status(thm)],[c_6292,c_22])).

tff(c_9316,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9305,c_6352])).

tff(c_9325,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_9316])).

tff(c_168,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,(
    ! [A_61,B_62] :
      ( ~ v1_xboole_0(A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_8191,plain,(
    ! [B_62] :
      ( v5_relat_1('#skF_6',B_62)
      | ~ v1_xboole_0(k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_178,c_8139])).

tff(c_8193,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_8191])).

tff(c_9327,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9325,c_8193])).

tff(c_9331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9327])).

tff(c_9366,plain,(
    ! [B_526] : v5_relat_1('#skF_6',B_526) ),
    inference(splitRight,[status(thm)],[c_8191])).

tff(c_9377,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9366,c_6352])).

tff(c_9386,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_9377])).

tff(c_9411,plain,(
    ! [B_483] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_483)))
      | ~ r1_tarski(k1_xboole_0,B_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9386,c_8085])).

tff(c_9489,plain,(
    ! [B_527] : m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_527))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6436,c_9411])).

tff(c_9512,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9489])).

tff(c_9551,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9512,c_30])).

tff(c_9637,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9551,c_22])).

tff(c_50,plain,(
    ! [A_38] :
      ( v1_funct_2(k1_xboole_0,A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_38,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    ! [A_38] :
      ( v1_funct_2(k1_xboole_0,A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_6514,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_6517,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_6514])).

tff(c_6521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6517])).

tff(c_6523,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_7179,plain,(
    ! [B_434,C_435] :
      ( k1_relset_1(k1_xboole_0,B_434,C_435) = k1_relat_1(C_435)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6804])).

tff(c_7185,plain,(
    ! [B_434] : k1_relset_1(k1_xboole_0,B_434,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6523,c_7179])).

tff(c_54,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6979,plain,(
    ! [C_421,B_422] :
      ( v1_funct_2(C_421,k1_xboole_0,B_422)
      | k1_relset_1(k1_xboole_0,B_422,C_421) != k1_xboole_0
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54])).

tff(c_6985,plain,(
    ! [B_422] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_422)
      | k1_relset_1(k1_xboole_0,B_422,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6523,c_6979])).

tff(c_7200,plain,(
    ! [B_422] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_422)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7185,c_6985])).

tff(c_7208,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7200])).

tff(c_7239,plain,(
    ! [A_443,C_444] :
      ( k1_relset_1(A_443,k1_xboole_0,C_444) = k1_relat_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6804])).

tff(c_7245,plain,(
    ! [A_443] : k1_relset_1(A_443,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6523,c_7239])).

tff(c_7285,plain,(
    ! [A_448,B_449,C_450] :
      ( m1_subset_1(k1_relset_1(A_448,B_449,C_450),k1_zfmisc_1(A_448))
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7326,plain,(
    ! [A_443] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_443))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_443,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7245,c_7285])).

tff(c_7386,plain,(
    ! [A_451] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_451)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6523,c_26,c_7326])).

tff(c_7487,plain,(
    ! [A_458] : r1_tarski(k1_relat_1(k1_xboole_0),A_458) ),
    inference(resolution,[status(thm)],[c_7386,c_30])).

tff(c_7554,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7487,c_22])).

tff(c_7593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7208,c_7554])).

tff(c_7595,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7200])).

tff(c_9673,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9637,c_9637,c_7595])).

tff(c_9708,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8037,c_9673])).

tff(c_9584,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9551,c_6674])).

tff(c_9617,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9584])).

tff(c_9720,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9708,c_9617])).

tff(c_9754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7738,c_9720])).

tff(c_9756,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7732])).

tff(c_179,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_191,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_179,c_22])).

tff(c_9771,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9756,c_191])).

tff(c_9822,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9771,c_9771,c_28])).

tff(c_118,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_139,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_126,c_14])).

tff(c_198,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_202,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_178,c_198])).

tff(c_10148,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9822,c_202])).

tff(c_10156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9756,c_10148])).

tff(c_10157,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k1_xboole_0 = B_17
      | k1_xboole_0 = A_16
      | k2_zfmisc_1(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10167,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_24])).

tff(c_10170,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_10167])).

tff(c_10187,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10170])).

tff(c_12691,plain,(
    ! [B_735,C_736,A_737] :
      ( k1_xboole_0 = B_735
      | v1_funct_2(C_736,A_737,B_735)
      | k1_relset_1(A_737,B_735,C_736) != A_737
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_737,B_735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_17282,plain,(
    ! [B_982,A_983,A_984] :
      ( k1_xboole_0 = B_982
      | v1_funct_2(A_983,A_984,B_982)
      | k1_relset_1(A_984,B_982,A_983) != A_984
      | ~ r1_tarski(A_983,k2_zfmisc_1(A_984,B_982)) ) ),
    inference(resolution,[status(thm)],[c_32,c_12691])).

tff(c_23318,plain,(
    ! [B_1216,A_1217,A_1218] :
      ( k1_xboole_0 = B_1216
      | v1_funct_2(A_1217,A_1218,B_1216)
      | k1_relset_1(A_1218,B_1216,A_1217) != A_1218
      | ~ v1_xboole_0(A_1217) ) ),
    inference(resolution,[status(thm)],[c_178,c_17282])).

tff(c_23351,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_23318,c_141])).

tff(c_23352,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_23351])).

tff(c_10160,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10157,c_68])).

tff(c_10378,plain,(
    ! [C_578,B_579,A_580] :
      ( v5_relat_1(C_578,B_579)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(A_580,B_579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10404,plain,(
    ! [C_585] :
      ( v5_relat_1(C_585,'#skF_4')
      | ~ m1_subset_1(C_585,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_10378])).

tff(c_10412,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_10160,c_10404])).

tff(c_10172,plain,(
    ! [A_546,C_547,B_548] :
      ( r1_tarski(A_546,C_547)
      | ~ r1_tarski(B_548,C_547)
      | ~ r1_tarski(A_546,B_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10188,plain,(
    ! [A_549] :
      ( r1_tarski(A_549,'#skF_5')
      | ~ r1_tarski(A_549,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_10172])).

tff(c_10361,plain,(
    ! [A_576,A_577] :
      ( r1_tarski(A_576,'#skF_5')
      | ~ r1_tarski(A_576,A_577)
      | ~ r1_tarski(A_577,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10188,c_20])).

tff(c_10436,plain,(
    ! [B_591,A_592] :
      ( r1_tarski(k2_relat_1(B_591),'#skF_5')
      | ~ r1_tarski(A_592,'#skF_4')
      | ~ v5_relat_1(B_591,A_592)
      | ~ v1_relat_1(B_591) ) ),
    inference(resolution,[status(thm)],[c_36,c_10361])).

tff(c_10440,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10412,c_10436])).

tff(c_10448,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_18,c_10440])).

tff(c_10484,plain,(
    ! [B_599,A_600] :
      ( v5_relat_1(B_599,A_600)
      | ~ r1_tarski(k2_relat_1(B_599),A_600)
      | ~ v1_relat_1(B_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10487,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10448,c_10484])).

tff(c_10505,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_10487])).

tff(c_11041,plain,(
    ! [A_645,B_646,C_647] :
      ( k1_relset_1(A_645,B_646,C_647) = k1_relat_1(C_647)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11181,plain,(
    ! [C_653] :
      ( k1_relset_1('#skF_3','#skF_4',C_653) = k1_relat_1(C_653)
      | ~ m1_subset_1(C_653,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_11041])).

tff(c_11189,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10160,c_11181])).

tff(c_11927,plain,(
    ! [B_696,A_697,C_698] :
      ( k1_xboole_0 = B_696
      | k1_relset_1(A_697,B_696,C_698) = A_697
      | ~ v1_funct_2(C_698,A_697,B_696)
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_697,B_696))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11934,plain,(
    ! [C_698] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_698) = '#skF_3'
      | ~ v1_funct_2(C_698,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_698,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_11927])).

tff(c_11966,plain,(
    ! [C_700] :
      ( k1_relset_1('#skF_3','#skF_4',C_700) = '#skF_3'
      | ~ v1_funct_2(C_700,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_700,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_11934])).

tff(c_11976,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10160,c_11966])).

tff(c_11986,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11189,c_11976])).

tff(c_11250,plain,(
    ! [A_658,B_659,C_660] :
      ( m1_subset_1(k1_relset_1(A_658,B_659,C_660),k1_zfmisc_1(A_658))
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11301,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11189,c_11250])).

tff(c_11319,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10160,c_10157,c_11301])).

tff(c_11323,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_11319,c_30])).

tff(c_11343,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_11323,c_14])).

tff(c_11350,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_11343])).

tff(c_11989,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11986,c_11350])).

tff(c_11995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11989])).

tff(c_11996,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11343])).

tff(c_10413,plain,(
    ! [A_18] :
      ( v5_relat_1(A_18,'#skF_4')
      | ~ r1_tarski(A_18,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_10404])).

tff(c_10438,plain,(
    ! [A_18] :
      ( r1_tarski(k2_relat_1(A_18),'#skF_5')
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ v1_relat_1(A_18)
      | ~ r1_tarski(A_18,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10413,c_10436])).

tff(c_10445,plain,(
    ! [A_18] :
      ( r1_tarski(k2_relat_1(A_18),'#skF_5')
      | ~ v1_relat_1(A_18)
      | ~ r1_tarski(A_18,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10438])).

tff(c_12237,plain,(
    ! [D_715,C_716,B_717,A_718] :
      ( m1_subset_1(D_715,k1_zfmisc_1(k2_zfmisc_1(C_716,B_717)))
      | ~ r1_tarski(k2_relat_1(D_715),B_717)
      | ~ m1_subset_1(D_715,k1_zfmisc_1(k2_zfmisc_1(C_716,A_718))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14687,plain,(
    ! [A_855,C_856,B_857,A_858] :
      ( m1_subset_1(A_855,k1_zfmisc_1(k2_zfmisc_1(C_856,B_857)))
      | ~ r1_tarski(k2_relat_1(A_855),B_857)
      | ~ r1_tarski(A_855,k2_zfmisc_1(C_856,A_858)) ) ),
    inference(resolution,[status(thm)],[c_32,c_12237])).

tff(c_28042,plain,(
    ! [C_1282,A_1283,B_1284] :
      ( m1_subset_1(k2_zfmisc_1(C_1282,A_1283),k1_zfmisc_1(k2_zfmisc_1(C_1282,B_1284)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(C_1282,A_1283)),B_1284) ) ),
    inference(resolution,[status(thm)],[c_18,c_14687])).

tff(c_28098,plain,(
    ! [B_1284] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1284)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')),B_1284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_28042])).

tff(c_30409,plain,(
    ! [B_1334] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1334)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_1334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10157,c_28098])).

tff(c_30780,plain,(
    ! [B_1342] :
      ( r1_tarski('#skF_6',k2_zfmisc_1('#skF_3',B_1342))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_1342) ) ),
    inference(resolution,[status(thm)],[c_30409,c_30])).

tff(c_30804,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_10445,c_30780])).

tff(c_30837,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_167,c_30804])).

tff(c_11055,plain,(
    ! [A_645,B_646,A_18] :
      ( k1_relset_1(A_645,B_646,A_18) = k1_relat_1(A_18)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_645,B_646)) ) ),
    inference(resolution,[status(thm)],[c_32,c_11041])).

tff(c_30863,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30837,c_11055])).

tff(c_30899,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11996,c_30863])).

tff(c_12720,plain,(
    ! [B_735,A_18,A_737] :
      ( k1_xboole_0 = B_735
      | v1_funct_2(A_18,A_737,B_735)
      | k1_relset_1(A_737,B_735,A_18) != A_737
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_737,B_735)) ) ),
    inference(resolution,[status(thm)],[c_32,c_12691])).

tff(c_30855,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_3','#skF_5')
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_30837,c_12720])).

tff(c_30895,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_30855])).

tff(c_31161,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30899,c_30895])).

tff(c_14334,plain,(
    ! [D_840,A_841,B_842] :
      ( m1_subset_1(D_840,k1_zfmisc_1(k2_zfmisc_1(A_841,B_842)))
      | ~ r1_tarski(k2_relat_1(D_840),B_842)
      | ~ m1_subset_1(D_840,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_12237])).

tff(c_26756,plain,(
    ! [D_1256,A_1257,B_1258] :
      ( r1_tarski(D_1256,k2_zfmisc_1(A_1257,B_1258))
      | ~ r1_tarski(k2_relat_1(D_1256),B_1258)
      | ~ m1_subset_1(D_1256,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14334,c_30])).

tff(c_26864,plain,(
    ! [A_1257] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_1257,'#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_10448,c_26756])).

tff(c_26939,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_26864])).

tff(c_30441,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_30409])).

tff(c_30455,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_26939,c_30441])).

tff(c_30467,plain,
    ( ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_30455])).

tff(c_30482,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_30467])).

tff(c_31162,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31161,c_30482])).

tff(c_31324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10505,c_31162])).

tff(c_31326,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_26864])).

tff(c_31368,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31326,c_30])).

tff(c_10196,plain,(
    ! [C_550] :
      ( v1_relat_1(C_550)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_10202,plain,(
    ! [A_551] :
      ( v1_relat_1(A_551)
      | ~ r1_tarski(A_551,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_10196])).

tff(c_10212,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_10202])).

tff(c_10577,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_10580,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_10577])).

tff(c_10584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10580])).

tff(c_10586,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_10388,plain,(
    ! [C_578,B_17] :
      ( v5_relat_1(C_578,B_17)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10378])).

tff(c_10598,plain,(
    ! [B_17] : v5_relat_1(k1_xboole_0,B_17) ),
    inference(resolution,[status(thm)],[c_10586,c_10388])).

tff(c_10605,plain,(
    ! [B_610] : v5_relat_1(k1_xboole_0,B_610) ),
    inference(resolution,[status(thm)],[c_10586,c_10388])).

tff(c_10324,plain,(
    ! [B_571,A_572] :
      ( r1_tarski(k2_relat_1(B_571),A_572)
      | ~ v5_relat_1(B_571,A_572)
      | ~ v1_relat_1(B_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10357,plain,(
    ! [B_571] :
      ( k2_relat_1(B_571) = k1_xboole_0
      | ~ v5_relat_1(B_571,k1_xboole_0)
      | ~ v1_relat_1(B_571) ) ),
    inference(resolution,[status(thm)],[c_10324,c_22])).

tff(c_10611,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10605,c_10357])).

tff(c_10617,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10212,c_10611])).

tff(c_10639,plain,(
    ! [A_20] :
      ( r1_tarski(k1_xboole_0,A_20)
      | ~ v5_relat_1(k1_xboole_0,A_20)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10617,c_36])).

tff(c_10655,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10212,c_10598,c_10639])).

tff(c_10219,plain,(
    ! [C_553,B_554,A_555] :
      ( r2_hidden(C_553,B_554)
      | ~ r2_hidden(C_553,A_555)
      | ~ r1_tarski(A_555,B_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10860,plain,(
    ! [A_633,B_634] :
      ( r2_hidden('#skF_1'(A_633),B_634)
      | ~ r1_tarski(A_633,B_634)
      | v1_xboole_0(A_633) ) ),
    inference(resolution,[status(thm)],[c_4,c_10219])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21547,plain,(
    ! [A_1148,B_1149,B_1150] :
      ( r2_hidden('#skF_1'(A_1148),B_1149)
      | ~ r1_tarski(B_1150,B_1149)
      | ~ r1_tarski(A_1148,B_1150)
      | v1_xboole_0(A_1148) ) ),
    inference(resolution,[status(thm)],[c_10860,c_6])).

tff(c_21661,plain,(
    ! [A_1152,A_1153] :
      ( r2_hidden('#skF_1'(A_1152),A_1153)
      | ~ r1_tarski(A_1152,k1_xboole_0)
      | v1_xboole_0(A_1152) ) ),
    inference(resolution,[status(thm)],[c_10655,c_21547])).

tff(c_21668,plain,(
    ! [A_1153,A_1152] :
      ( ~ v1_xboole_0(A_1153)
      | ~ r1_tarski(A_1152,k1_xboole_0)
      | v1_xboole_0(A_1152) ) ),
    inference(resolution,[status(thm)],[c_21661,c_2])).

tff(c_21669,plain,(
    ! [A_1153] : ~ v1_xboole_0(A_1153) ),
    inference(splitLeft,[status(thm)],[c_21668])).

tff(c_21798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21669,c_12])).

tff(c_21799,plain,(
    ! [A_1152] :
      ( ~ r1_tarski(A_1152,k1_xboole_0)
      | v1_xboole_0(A_1152) ) ),
    inference(splitRight,[status(thm)],[c_21668])).

tff(c_31554,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_31368,c_21799])).

tff(c_31595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23352,c_31554])).

tff(c_31597,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_23351])).

tff(c_31634,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_31597,c_191])).

tff(c_31658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10187,c_31634])).

tff(c_31659,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10170])).

tff(c_31660,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10170])).

tff(c_31679,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_31660])).

tff(c_31680,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31679,c_31679,c_10160])).

tff(c_31664,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_31659,c_28])).

tff(c_32382,plain,(
    ! [A_1440,B_1441,C_1442] :
      ( k1_relset_1(A_1440,B_1441,C_1442) = k1_relat_1(C_1442)
      | ~ m1_subset_1(C_1442,k1_zfmisc_1(k2_zfmisc_1(A_1440,B_1441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_33274,plain,(
    ! [B_1506,C_1507] :
      ( k1_relset_1('#skF_3',B_1506,C_1507) = k1_relat_1(C_1507)
      | ~ m1_subset_1(C_1507,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31664,c_32382])).

tff(c_33285,plain,(
    ! [B_1506] : k1_relset_1('#skF_3',B_1506,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_31680,c_33274])).

tff(c_76,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54])).

tff(c_32805,plain,(
    ! [C_1471,B_1472] :
      ( v1_funct_2(C_1471,'#skF_3',B_1472)
      | k1_relset_1('#skF_3',B_1472,C_1471) != '#skF_3'
      | ~ m1_subset_1(C_1471,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_31659,c_31659,c_31659,c_76])).

tff(c_32968,plain,(
    ! [B_1480] :
      ( v1_funct_2('#skF_3','#skF_3',B_1480)
      | k1_relset_1('#skF_3',B_1480,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_31680,c_32805])).

tff(c_31683,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31679,c_141])).

tff(c_32984,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_32968,c_31683])).

tff(c_33288,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33285,c_32984])).

tff(c_31684,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31679,c_70])).

tff(c_58,plain,(
    ! [B_39,C_40] :
      ( k1_relset_1(k1_xboole_0,B_39,C_40) = k1_xboole_0
      | ~ v1_funct_2(C_40,k1_xboole_0,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,(
    ! [B_39,C_40] :
      ( k1_relset_1(k1_xboole_0,B_39,C_40) = k1_xboole_0
      | ~ v1_funct_2(C_40,k1_xboole_0,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_32580,plain,(
    ! [B_1456,C_1457] :
      ( k1_relset_1('#skF_3',B_1456,C_1457) = '#skF_3'
      | ~ v1_funct_2(C_1457,'#skF_3',B_1456)
      | ~ m1_subset_1(C_1457,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_31659,c_31659,c_31659,c_75])).

tff(c_32585,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_31684,c_32580])).

tff(c_32592,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31680,c_32585])).

tff(c_33290,plain,(
    ! [B_1508] : k1_relset_1('#skF_3',B_1508,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_31680,c_33274])).

tff(c_33304,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_32592,c_33290])).

tff(c_33311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33288,c_33304])).

tff(c_33312,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_35124,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_35092,c_33312])).

tff(c_35131,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_35124])).

tff(c_35143,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33332,c_35131])).

tff(c_35148,plain,
    ( ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_33712,c_35143])).

tff(c_35158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33332,c_33625,c_35148])).

tff(c_35160,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_35177,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_4',B_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35160,c_35160,c_28])).

tff(c_35159,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_35166,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35160,c_35159])).

tff(c_35201,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35177,c_35166,c_68])).

tff(c_35217,plain,(
    ! [A_1687,B_1688] :
      ( r1_tarski(A_1687,B_1688)
      | ~ m1_subset_1(A_1687,k1_zfmisc_1(B_1688)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35225,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_35201,c_35217])).

tff(c_35202,plain,(
    ! [A_15] :
      ( A_15 = '#skF_4'
      | ~ r1_tarski(A_15,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35160,c_35160,c_22])).

tff(c_35229,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35225,c_35202])).

tff(c_35232,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35229,c_35201])).

tff(c_36230,plain,(
    ! [A_1815,B_1816,C_1817] :
      ( k1_relset_1(A_1815,B_1816,C_1817) = k1_relat_1(C_1817)
      | ~ m1_subset_1(C_1817,k1_zfmisc_1(k2_zfmisc_1(A_1815,B_1816))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36392,plain,(
    ! [B_1822,C_1823] :
      ( k1_relset_1('#skF_4',B_1822,C_1823) = k1_relat_1(C_1823)
      | ~ m1_subset_1(C_1823,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35177,c_36230])).

tff(c_36398,plain,(
    ! [B_1822] : k1_relset_1('#skF_4',B_1822,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_35232,c_36392])).

tff(c_36401,plain,(
    ! [C_1824,B_1825] :
      ( v1_funct_2(C_1824,'#skF_4',B_1825)
      | k1_relset_1('#skF_4',B_1825,C_1824) != '#skF_4'
      | ~ m1_subset_1(C_1824,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35160,c_35160,c_35160,c_35160,c_76])).

tff(c_36407,plain,(
    ! [B_1825] :
      ( v1_funct_2('#skF_4','#skF_4',B_1825)
      | k1_relset_1('#skF_4',B_1825,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_35232,c_36401])).

tff(c_36453,plain,(
    ! [B_1825] :
      ( v1_funct_2('#skF_4','#skF_4',B_1825)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36398,c_36407])).

tff(c_36454,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36453])).

tff(c_35172,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35166,c_70])).

tff(c_35231,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35229,c_35172])).

tff(c_36516,plain,(
    ! [B_1838,C_1839] :
      ( k1_relset_1('#skF_4',B_1838,C_1839) = '#skF_4'
      | ~ v1_funct_2(C_1839,'#skF_4',B_1838)
      | ~ m1_subset_1(C_1839,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35160,c_35160,c_35160,c_35160,c_75])).

tff(c_36521,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_35231,c_36516])).

tff(c_36529,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35232,c_36398,c_36521])).

tff(c_36531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36454,c_36529])).

tff(c_36532,plain,(
    ! [B_1825] : v1_funct_2('#skF_4','#skF_4',B_1825) ),
    inference(splitRight,[status(thm)],[c_36453])).

tff(c_35239,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35229,c_35166,c_35229,c_35177,c_35166,c_74])).

tff(c_35240,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35239])).

tff(c_36542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36532,c_35240])).

tff(c_36543,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_35239])).

tff(c_36551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35232,c_36543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.58/5.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.58/5.75  
% 13.58/5.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.58/5.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 13.58/5.75  
% 13.58/5.75  %Foreground sorts:
% 13.58/5.75  
% 13.58/5.75  
% 13.58/5.75  %Background operators:
% 13.58/5.75  
% 13.58/5.75  
% 13.58/5.75  %Foreground operators:
% 13.58/5.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.58/5.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.58/5.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.58/5.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.58/5.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.58/5.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.58/5.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.58/5.75  tff('#skF_5', type, '#skF_5': $i).
% 13.58/5.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.58/5.75  tff('#skF_6', type, '#skF_6': $i).
% 13.58/5.75  tff('#skF_3', type, '#skF_3': $i).
% 13.58/5.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.58/5.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.58/5.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.58/5.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.58/5.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.58/5.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.58/5.75  tff('#skF_4', type, '#skF_4': $i).
% 13.58/5.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.58/5.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.58/5.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.58/5.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.58/5.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.58/5.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.58/5.75  
% 13.97/5.79  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 13.97/5.79  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.97/5.79  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.97/5.79  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 13.97/5.79  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.97/5.79  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 13.97/5.79  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.97/5.79  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 13.97/5.79  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.97/5.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.97/5.79  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.97/5.79  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.97/5.79  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.97/5.79  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.97/5.79  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 13.97/5.79  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.97/5.79  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_33319, plain, (![C_1511, A_1512, B_1513]: (v1_relat_1(C_1511) | ~m1_subset_1(C_1511, k1_zfmisc_1(k2_zfmisc_1(A_1512, B_1513))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.97/5.79  tff(c_33332, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_33319])).
% 13.97/5.79  tff(c_33610, plain, (![C_1560, B_1561, A_1562]: (v5_relat_1(C_1560, B_1561) | ~m1_subset_1(C_1560, k1_zfmisc_1(k2_zfmisc_1(A_1562, B_1561))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.97/5.79  tff(c_33625, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_33610])).
% 13.97/5.79  tff(c_33672, plain, (![B_1576, A_1577]: (r1_tarski(k2_relat_1(B_1576), A_1577) | ~v5_relat_1(B_1576, A_1577) | ~v1_relat_1(B_1576))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.79  tff(c_66, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_33496, plain, (![A_1545, C_1546, B_1547]: (r1_tarski(A_1545, C_1546) | ~r1_tarski(B_1547, C_1546) | ~r1_tarski(A_1545, B_1547))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.97/5.79  tff(c_33509, plain, (![A_1548]: (r1_tarski(A_1548, '#skF_5') | ~r1_tarski(A_1548, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_33496])).
% 13.97/5.79  tff(c_34, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.79  tff(c_33523, plain, (![B_21]: (v5_relat_1(B_21, '#skF_5') | ~v1_relat_1(B_21) | ~r1_tarski(k2_relat_1(B_21), '#skF_4'))), inference(resolution, [status(thm)], [c_33509, c_34])).
% 13.97/5.79  tff(c_33712, plain, (![B_1576]: (v5_relat_1(B_1576, '#skF_5') | ~v5_relat_1(B_1576, '#skF_4') | ~v1_relat_1(B_1576))), inference(resolution, [status(thm)], [c_33672, c_33523])).
% 13.97/5.79  tff(c_36, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.79  tff(c_35068, plain, (![D_1674, C_1675, B_1676, A_1677]: (m1_subset_1(D_1674, k1_zfmisc_1(k2_zfmisc_1(C_1675, B_1676))) | ~r1_tarski(k2_relat_1(D_1674), B_1676) | ~m1_subset_1(D_1674, k1_zfmisc_1(k2_zfmisc_1(C_1675, A_1677))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.97/5.79  tff(c_35092, plain, (![B_1678]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1678))) | ~r1_tarski(k2_relat_1('#skF_6'), B_1678))), inference(resolution, [status(thm)], [c_68, c_35068])).
% 13.97/5.79  tff(c_64, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_81, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 13.97/5.79  tff(c_6804, plain, (![A_412, B_413, C_414]: (k1_relset_1(A_412, B_413, C_414)=k1_relat_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.97/5.79  tff(c_6819, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_6804])).
% 13.97/5.79  tff(c_7647, plain, (![A_463, B_464, C_465]: (m1_subset_1(k1_relset_1(A_463, B_464, C_465), k1_zfmisc_1(A_463)) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.97/5.79  tff(c_7688, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6819, c_7647])).
% 13.97/5.79  tff(c_7707, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7688])).
% 13.97/5.79  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.97/5.79  tff(c_7711, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_7707, c_30])).
% 13.97/5.79  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.97/5.79  tff(c_6206, plain, (![C_374, B_375, A_376]: (r2_hidden(C_374, B_375) | ~r2_hidden(C_374, A_376) | ~r1_tarski(A_376, B_375))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.97/5.79  tff(c_6667, plain, (![A_404, B_405]: (r2_hidden('#skF_1'(A_404), B_405) | ~r1_tarski(A_404, B_405) | v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_4, c_6206])).
% 13.97/5.79  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.97/5.79  tff(c_6674, plain, (![B_405, A_404]: (~v1_xboole_0(B_405) | ~r1_tarski(A_404, B_405) | v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_6667, c_2])).
% 13.97/5.79  tff(c_7732, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7711, c_6674])).
% 13.97/5.79  tff(c_7738, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_7732])).
% 13.97/5.79  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.97/5.79  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_8000, plain, (![B_476, A_477, C_478]: (k1_xboole_0=B_476 | k1_relset_1(A_477, B_476, C_478)=A_477 | ~v1_funct_2(C_478, A_477, B_476) | ~m1_subset_1(C_478, k1_zfmisc_1(k2_zfmisc_1(A_477, B_476))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.79  tff(c_8014, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_8000])).
% 13.97/5.79  tff(c_8026, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6819, c_8014])).
% 13.97/5.79  tff(c_8027, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_81, c_8026])).
% 13.97/5.79  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.97/5.79  tff(c_7737, plain, (k1_relat_1('#skF_6')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7711, c_14])).
% 13.97/5.79  tff(c_7744, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_7737])).
% 13.97/5.79  tff(c_8030, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_7744])).
% 13.97/5.79  tff(c_8036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_8030])).
% 13.97/5.79  tff(c_8037, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_7737])).
% 13.97/5.79  tff(c_26, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.97/5.79  tff(c_32, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.97/5.79  tff(c_28, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.97/5.79  tff(c_154, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.97/5.79  tff(c_203, plain, (![C_66]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_154])).
% 13.97/5.79  tff(c_209, plain, (![A_67]: (v1_relat_1(A_67) | ~r1_tarski(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_203])).
% 13.97/5.79  tff(c_219, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_209])).
% 13.97/5.79  tff(c_326, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.97/5.79  tff(c_365, plain, (![A_92, B_93, A_94]: (v5_relat_1(A_92, B_93) | ~r1_tarski(A_92, k2_zfmisc_1(A_94, B_93)))), inference(resolution, [status(thm)], [c_32, c_326])).
% 13.97/5.79  tff(c_392, plain, (![A_97, B_98]: (v5_relat_1(k2_zfmisc_1(A_97, B_98), B_98))), inference(resolution, [status(thm)], [c_18, c_365])).
% 13.97/5.79  tff(c_395, plain, (![B_17]: (v5_relat_1(k1_xboole_0, B_17))), inference(superposition, [status(thm), theory('equality')], [c_28, c_392])).
% 13.97/5.79  tff(c_253, plain, (![A_74, A_75, B_76]: (v1_relat_1(A_74) | ~r1_tarski(A_74, k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_32, c_154])).
% 13.97/5.79  tff(c_276, plain, (![A_75, B_76]: (v1_relat_1(k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_18, c_253])).
% 13.97/5.79  tff(c_390, plain, (![A_94, B_93]: (v5_relat_1(k2_zfmisc_1(A_94, B_93), B_93))), inference(resolution, [status(thm)], [c_18, c_365])).
% 13.97/5.79  tff(c_6292, plain, (![B_387, A_388]: (r1_tarski(k2_relat_1(B_387), A_388) | ~v5_relat_1(B_387, A_388) | ~v1_relat_1(B_387))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.79  tff(c_22, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.97/5.79  tff(c_6393, plain, (![B_390]: (k2_relat_1(B_390)=k1_xboole_0 | ~v5_relat_1(B_390, k1_xboole_0) | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_6292, c_22])).
% 13.97/5.79  tff(c_6401, plain, (![A_94]: (k2_relat_1(k2_zfmisc_1(A_94, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_94, k1_xboole_0)))), inference(resolution, [status(thm)], [c_390, c_6393])).
% 13.97/5.79  tff(c_6415, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_276, c_26, c_6401])).
% 13.97/5.79  tff(c_6421, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20) | ~v5_relat_1(k1_xboole_0, A_20) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6415, c_36])).
% 13.97/5.79  tff(c_6436, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_395, c_6421])).
% 13.97/5.79  tff(c_167, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_154])).
% 13.97/5.79  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.97/5.79  tff(c_342, plain, (![C_87, B_88]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_326])).
% 13.97/5.79  tff(c_346, plain, (![A_18, B_88]: (v5_relat_1(A_18, B_88) | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_342])).
% 13.97/5.79  tff(c_6447, plain, (![A_391]: (r1_tarski(k1_xboole_0, A_391))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_395, c_6421])).
% 13.97/5.79  tff(c_20, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.97/5.79  tff(c_6544, plain, (![A_394, A_395]: (r1_tarski(A_394, A_395) | ~r1_tarski(A_394, k1_xboole_0))), inference(resolution, [status(thm)], [c_6447, c_20])).
% 13.97/5.79  tff(c_6559, plain, (![B_21, A_395]: (r1_tarski(k2_relat_1(B_21), A_395) | ~v5_relat_1(B_21, k1_xboole_0) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_36, c_6544])).
% 13.97/5.79  tff(c_8070, plain, (![D_481, C_482, B_483, A_484]: (m1_subset_1(D_481, k1_zfmisc_1(k2_zfmisc_1(C_482, B_483))) | ~r1_tarski(k2_relat_1(D_481), B_483) | ~m1_subset_1(D_481, k1_zfmisc_1(k2_zfmisc_1(C_482, A_484))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.97/5.79  tff(c_8108, plain, (![B_489]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_489))) | ~r1_tarski(k2_relat_1('#skF_6'), B_489))), inference(resolution, [status(thm)], [c_68, c_8070])).
% 13.97/5.79  tff(c_40, plain, (![C_27, B_26, A_25]: (v5_relat_1(C_27, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.97/5.79  tff(c_8139, plain, (![B_490]: (v5_relat_1('#skF_6', B_490) | ~r1_tarski(k2_relat_1('#skF_6'), B_490))), inference(resolution, [status(thm)], [c_8108, c_40])).
% 13.97/5.79  tff(c_8151, plain, (![A_395]: (v5_relat_1('#skF_6', A_395) | ~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6559, c_8139])).
% 13.97/5.79  tff(c_8184, plain, (![A_395]: (v5_relat_1('#skF_6', A_395) | ~v5_relat_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_8151])).
% 13.97/5.79  tff(c_8194, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8184])).
% 13.97/5.79  tff(c_8231, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_346, c_8194])).
% 13.97/5.79  tff(c_341, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_326])).
% 13.97/5.79  tff(c_220, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.97/5.79  tff(c_232, plain, (![A_68]: (r1_tarski(A_68, '#skF_5') | ~r1_tarski(A_68, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_220])).
% 13.97/5.79  tff(c_8190, plain, (v5_relat_1('#skF_6', '#skF_5') | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_232, c_8139])).
% 13.97/5.79  tff(c_8236, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8190])).
% 13.97/5.79  tff(c_8245, plain, (~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_8236])).
% 13.97/5.79  tff(c_8258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_341, c_8245])).
% 13.97/5.79  tff(c_8260, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_8190])).
% 13.97/5.79  tff(c_239, plain, (![A_72]: (r1_tarski(A_72, '#skF_5') | ~r1_tarski(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_220])).
% 13.97/5.79  tff(c_244, plain, (![A_12, A_72]: (r1_tarski(A_12, '#skF_5') | ~r1_tarski(A_12, A_72) | ~r1_tarski(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_239, c_20])).
% 13.97/5.79  tff(c_8280, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_8260, c_244])).
% 13.97/5.79  tff(c_8303, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8280])).
% 13.97/5.79  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_62, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.97/5.79  tff(c_74, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 13.97/5.79  tff(c_141, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 13.97/5.79  tff(c_8605, plain, (![B_505]: (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', B_505)) | ~r1_tarski(k2_relat_1('#skF_6'), B_505))), inference(resolution, [status(thm)], [c_8108, c_30])).
% 13.97/5.79  tff(c_8639, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_5')) | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_232, c_8605])).
% 13.97/5.79  tff(c_8667, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8260, c_8639])).
% 13.97/5.79  tff(c_8763, plain, (![A_506, B_507, A_508]: (k1_relset_1(A_506, B_507, A_508)=k1_relat_1(A_508) | ~r1_tarski(A_508, k2_zfmisc_1(A_506, B_507)))), inference(resolution, [status(thm)], [c_32, c_6804])).
% 13.97/5.79  tff(c_8769, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8667, c_8763])).
% 13.97/5.79  tff(c_8805, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8037, c_8769])).
% 13.97/5.79  tff(c_8085, plain, (![B_483]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_483))) | ~r1_tarski(k2_relat_1('#skF_6'), B_483))), inference(resolution, [status(thm)], [c_68, c_8070])).
% 13.97/5.79  tff(c_8195, plain, (![B_491, C_492, A_493]: (k1_xboole_0=B_491 | v1_funct_2(C_492, A_493, B_491) | k1_relset_1(A_493, B_491, C_492)!=A_493 | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_493, B_491))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.79  tff(c_9137, plain, (![B_521]: (k1_xboole_0=B_521 | v1_funct_2('#skF_6', '#skF_3', B_521) | k1_relset_1('#skF_3', B_521, '#skF_6')!='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), B_521))), inference(resolution, [status(thm)], [c_8085, c_8195])).
% 13.97/5.79  tff(c_9175, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_3', '#skF_5') | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_232, c_9137])).
% 13.97/5.79  tff(c_9214, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8260, c_8805, c_9175])).
% 13.97/5.79  tff(c_9215, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_141, c_9214])).
% 13.97/5.79  tff(c_8129, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_8108])).
% 13.97/5.79  tff(c_8410, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8129])).
% 13.97/5.79  tff(c_9225, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9215, c_8410])).
% 13.97/5.79  tff(c_9269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8303, c_9225])).
% 13.97/5.79  tff(c_9270, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_8129])).
% 13.97/5.79  tff(c_9287, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_9270, c_30])).
% 13.97/5.79  tff(c_9299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8231, c_9287])).
% 13.97/5.79  tff(c_9305, plain, (![A_522]: (v5_relat_1('#skF_6', A_522))), inference(splitRight, [status(thm)], [c_8184])).
% 13.97/5.79  tff(c_6352, plain, (![B_387]: (k2_relat_1(B_387)=k1_xboole_0 | ~v5_relat_1(B_387, k1_xboole_0) | ~v1_relat_1(B_387))), inference(resolution, [status(thm)], [c_6292, c_22])).
% 13.97/5.79  tff(c_9316, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_9305, c_6352])).
% 13.97/5.79  tff(c_9325, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_9316])).
% 13.97/5.79  tff(c_168, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.97/5.79  tff(c_178, plain, (![A_61, B_62]: (~v1_xboole_0(A_61) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_168, c_2])).
% 13.97/5.79  tff(c_8191, plain, (![B_62]: (v5_relat_1('#skF_6', B_62) | ~v1_xboole_0(k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_178, c_8139])).
% 13.97/5.79  tff(c_8193, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_8191])).
% 13.97/5.79  tff(c_9327, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9325, c_8193])).
% 13.97/5.79  tff(c_9331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_9327])).
% 13.97/5.79  tff(c_9366, plain, (![B_526]: (v5_relat_1('#skF_6', B_526))), inference(splitRight, [status(thm)], [c_8191])).
% 13.97/5.79  tff(c_9377, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_9366, c_6352])).
% 13.97/5.79  tff(c_9386, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_9377])).
% 13.97/5.79  tff(c_9411, plain, (![B_483]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_483))) | ~r1_tarski(k1_xboole_0, B_483))), inference(demodulation, [status(thm), theory('equality')], [c_9386, c_8085])).
% 13.97/5.79  tff(c_9489, plain, (![B_527]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_527))))), inference(demodulation, [status(thm), theory('equality')], [c_6436, c_9411])).
% 13.97/5.79  tff(c_9512, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9489])).
% 13.97/5.79  tff(c_9551, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_9512, c_30])).
% 13.97/5.79  tff(c_9637, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9551, c_22])).
% 13.97/5.79  tff(c_50, plain, (![A_38]: (v1_funct_2(k1_xboole_0, A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_38, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.79  tff(c_77, plain, (![A_38]: (v1_funct_2(k1_xboole_0, A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_50])).
% 13.97/5.79  tff(c_6514, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_77])).
% 13.97/5.79  tff(c_6517, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_6514])).
% 13.97/5.79  tff(c_6521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_6517])).
% 13.97/5.79  tff(c_6523, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_77])).
% 13.97/5.79  tff(c_7179, plain, (![B_434, C_435]: (k1_relset_1(k1_xboole_0, B_434, C_435)=k1_relat_1(C_435) | ~m1_subset_1(C_435, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6804])).
% 13.97/5.79  tff(c_7185, plain, (![B_434]: (k1_relset_1(k1_xboole_0, B_434, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6523, c_7179])).
% 13.97/5.79  tff(c_54, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.79  tff(c_6979, plain, (![C_421, B_422]: (v1_funct_2(C_421, k1_xboole_0, B_422) | k1_relset_1(k1_xboole_0, B_422, C_421)!=k1_xboole_0 | ~m1_subset_1(C_421, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_54])).
% 13.97/5.79  tff(c_6985, plain, (![B_422]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_422) | k1_relset_1(k1_xboole_0, B_422, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6523, c_6979])).
% 13.97/5.79  tff(c_7200, plain, (![B_422]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_422) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7185, c_6985])).
% 13.97/5.79  tff(c_7208, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7200])).
% 13.97/5.79  tff(c_7239, plain, (![A_443, C_444]: (k1_relset_1(A_443, k1_xboole_0, C_444)=k1_relat_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_6804])).
% 13.97/5.79  tff(c_7245, plain, (![A_443]: (k1_relset_1(A_443, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6523, c_7239])).
% 13.97/5.79  tff(c_7285, plain, (![A_448, B_449, C_450]: (m1_subset_1(k1_relset_1(A_448, B_449, C_450), k1_zfmisc_1(A_448)) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.97/5.79  tff(c_7326, plain, (![A_443]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_443)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_443, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_7245, c_7285])).
% 13.97/5.79  tff(c_7386, plain, (![A_451]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_451)))), inference(demodulation, [status(thm), theory('equality')], [c_6523, c_26, c_7326])).
% 13.97/5.79  tff(c_7487, plain, (![A_458]: (r1_tarski(k1_relat_1(k1_xboole_0), A_458))), inference(resolution, [status(thm)], [c_7386, c_30])).
% 13.97/5.79  tff(c_7554, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_7487, c_22])).
% 13.97/5.79  tff(c_7593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7208, c_7554])).
% 13.97/5.79  tff(c_7595, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7200])).
% 13.97/5.79  tff(c_9673, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9637, c_9637, c_7595])).
% 13.97/5.79  tff(c_9708, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8037, c_9673])).
% 13.97/5.79  tff(c_9584, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9551, c_6674])).
% 13.97/5.79  tff(c_9617, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9584])).
% 13.97/5.79  tff(c_9720, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9708, c_9617])).
% 13.97/5.79  tff(c_9754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7738, c_9720])).
% 13.97/5.79  tff(c_9756, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_7732])).
% 13.97/5.79  tff(c_179, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_168, c_2])).
% 13.97/5.79  tff(c_191, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_179, c_22])).
% 13.97/5.79  tff(c_9771, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9756, c_191])).
% 13.97/5.79  tff(c_9822, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9771, c_9771, c_28])).
% 13.97/5.79  tff(c_118, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.97/5.80  tff(c_126, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_118])).
% 13.97/5.80  tff(c_139, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_126, c_14])).
% 13.97/5.80  tff(c_198, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_139])).
% 13.97/5.80  tff(c_202, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_178, c_198])).
% 13.97/5.80  tff(c_10148, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9822, c_202])).
% 13.97/5.80  tff(c_10156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9756, c_10148])).
% 13.97/5.80  tff(c_10157, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_139])).
% 13.97/5.80  tff(c_24, plain, (![B_17, A_16]: (k1_xboole_0=B_17 | k1_xboole_0=A_16 | k2_zfmisc_1(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.97/5.80  tff(c_10167, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10157, c_24])).
% 13.97/5.80  tff(c_10170, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_81, c_10167])).
% 13.97/5.80  tff(c_10187, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_10170])).
% 13.97/5.80  tff(c_12691, plain, (![B_735, C_736, A_737]: (k1_xboole_0=B_735 | v1_funct_2(C_736, A_737, B_735) | k1_relset_1(A_737, B_735, C_736)!=A_737 | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_737, B_735))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.80  tff(c_17282, plain, (![B_982, A_983, A_984]: (k1_xboole_0=B_982 | v1_funct_2(A_983, A_984, B_982) | k1_relset_1(A_984, B_982, A_983)!=A_984 | ~r1_tarski(A_983, k2_zfmisc_1(A_984, B_982)))), inference(resolution, [status(thm)], [c_32, c_12691])).
% 13.97/5.80  tff(c_23318, plain, (![B_1216, A_1217, A_1218]: (k1_xboole_0=B_1216 | v1_funct_2(A_1217, A_1218, B_1216) | k1_relset_1(A_1218, B_1216, A_1217)!=A_1218 | ~v1_xboole_0(A_1217))), inference(resolution, [status(thm)], [c_178, c_17282])).
% 13.97/5.80  tff(c_23351, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_23318, c_141])).
% 13.97/5.80  tff(c_23352, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_23351])).
% 13.97/5.80  tff(c_10160, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10157, c_68])).
% 13.97/5.80  tff(c_10378, plain, (![C_578, B_579, A_580]: (v5_relat_1(C_578, B_579) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(A_580, B_579))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.97/5.80  tff(c_10404, plain, (![C_585]: (v5_relat_1(C_585, '#skF_4') | ~m1_subset_1(C_585, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10157, c_10378])).
% 13.97/5.80  tff(c_10412, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_10160, c_10404])).
% 13.97/5.80  tff(c_10172, plain, (![A_546, C_547, B_548]: (r1_tarski(A_546, C_547) | ~r1_tarski(B_548, C_547) | ~r1_tarski(A_546, B_548))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.97/5.80  tff(c_10188, plain, (![A_549]: (r1_tarski(A_549, '#skF_5') | ~r1_tarski(A_549, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_10172])).
% 13.97/5.80  tff(c_10361, plain, (![A_576, A_577]: (r1_tarski(A_576, '#skF_5') | ~r1_tarski(A_576, A_577) | ~r1_tarski(A_577, '#skF_4'))), inference(resolution, [status(thm)], [c_10188, c_20])).
% 13.97/5.80  tff(c_10436, plain, (![B_591, A_592]: (r1_tarski(k2_relat_1(B_591), '#skF_5') | ~r1_tarski(A_592, '#skF_4') | ~v5_relat_1(B_591, A_592) | ~v1_relat_1(B_591))), inference(resolution, [status(thm)], [c_36, c_10361])).
% 13.97/5.80  tff(c_10440, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10412, c_10436])).
% 13.97/5.80  tff(c_10448, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_18, c_10440])).
% 13.97/5.80  tff(c_10484, plain, (![B_599, A_600]: (v5_relat_1(B_599, A_600) | ~r1_tarski(k2_relat_1(B_599), A_600) | ~v1_relat_1(B_599))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.80  tff(c_10487, plain, (v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10448, c_10484])).
% 13.97/5.80  tff(c_10505, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_10487])).
% 13.97/5.80  tff(c_11041, plain, (![A_645, B_646, C_647]: (k1_relset_1(A_645, B_646, C_647)=k1_relat_1(C_647) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_646))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.97/5.80  tff(c_11181, plain, (![C_653]: (k1_relset_1('#skF_3', '#skF_4', C_653)=k1_relat_1(C_653) | ~m1_subset_1(C_653, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10157, c_11041])).
% 13.97/5.80  tff(c_11189, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10160, c_11181])).
% 13.97/5.80  tff(c_11927, plain, (![B_696, A_697, C_698]: (k1_xboole_0=B_696 | k1_relset_1(A_697, B_696, C_698)=A_697 | ~v1_funct_2(C_698, A_697, B_696) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_697, B_696))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.80  tff(c_11934, plain, (![C_698]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_698)='#skF_3' | ~v1_funct_2(C_698, '#skF_3', '#skF_4') | ~m1_subset_1(C_698, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10157, c_11927])).
% 13.97/5.80  tff(c_11966, plain, (![C_700]: (k1_relset_1('#skF_3', '#skF_4', C_700)='#skF_3' | ~v1_funct_2(C_700, '#skF_3', '#skF_4') | ~m1_subset_1(C_700, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_81, c_11934])).
% 13.97/5.80  tff(c_11976, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10160, c_11966])).
% 13.97/5.80  tff(c_11986, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_11189, c_11976])).
% 13.97/5.80  tff(c_11250, plain, (![A_658, B_659, C_660]: (m1_subset_1(k1_relset_1(A_658, B_659, C_660), k1_zfmisc_1(A_658)) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.97/5.80  tff(c_11301, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11189, c_11250])).
% 13.97/5.80  tff(c_11319, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10160, c_10157, c_11301])).
% 13.97/5.80  tff(c_11323, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_11319, c_30])).
% 13.97/5.80  tff(c_11343, plain, (k1_relat_1('#skF_6')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_11323, c_14])).
% 13.97/5.80  tff(c_11350, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_11343])).
% 13.97/5.80  tff(c_11989, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11986, c_11350])).
% 13.97/5.80  tff(c_11995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_11989])).
% 13.97/5.80  tff(c_11996, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_11343])).
% 13.97/5.80  tff(c_10413, plain, (![A_18]: (v5_relat_1(A_18, '#skF_4') | ~r1_tarski(A_18, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_10404])).
% 13.97/5.80  tff(c_10438, plain, (![A_18]: (r1_tarski(k2_relat_1(A_18), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(A_18) | ~r1_tarski(A_18, '#skF_6'))), inference(resolution, [status(thm)], [c_10413, c_10436])).
% 13.97/5.80  tff(c_10445, plain, (![A_18]: (r1_tarski(k2_relat_1(A_18), '#skF_5') | ~v1_relat_1(A_18) | ~r1_tarski(A_18, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10438])).
% 13.97/5.80  tff(c_12237, plain, (![D_715, C_716, B_717, A_718]: (m1_subset_1(D_715, k1_zfmisc_1(k2_zfmisc_1(C_716, B_717))) | ~r1_tarski(k2_relat_1(D_715), B_717) | ~m1_subset_1(D_715, k1_zfmisc_1(k2_zfmisc_1(C_716, A_718))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.97/5.80  tff(c_14687, plain, (![A_855, C_856, B_857, A_858]: (m1_subset_1(A_855, k1_zfmisc_1(k2_zfmisc_1(C_856, B_857))) | ~r1_tarski(k2_relat_1(A_855), B_857) | ~r1_tarski(A_855, k2_zfmisc_1(C_856, A_858)))), inference(resolution, [status(thm)], [c_32, c_12237])).
% 13.97/5.80  tff(c_28042, plain, (![C_1282, A_1283, B_1284]: (m1_subset_1(k2_zfmisc_1(C_1282, A_1283), k1_zfmisc_1(k2_zfmisc_1(C_1282, B_1284))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(C_1282, A_1283)), B_1284))), inference(resolution, [status(thm)], [c_18, c_14687])).
% 13.97/5.80  tff(c_28098, plain, (![B_1284]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1284))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')), B_1284))), inference(superposition, [status(thm), theory('equality')], [c_10157, c_28042])).
% 13.97/5.80  tff(c_30409, plain, (![B_1334]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1334))) | ~r1_tarski(k2_relat_1('#skF_6'), B_1334))), inference(demodulation, [status(thm), theory('equality')], [c_10157, c_28098])).
% 13.97/5.80  tff(c_30780, plain, (![B_1342]: (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', B_1342)) | ~r1_tarski(k2_relat_1('#skF_6'), B_1342))), inference(resolution, [status(thm)], [c_30409, c_30])).
% 13.97/5.80  tff(c_30804, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_10445, c_30780])).
% 13.97/5.80  tff(c_30837, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_167, c_30804])).
% 13.97/5.80  tff(c_11055, plain, (![A_645, B_646, A_18]: (k1_relset_1(A_645, B_646, A_18)=k1_relat_1(A_18) | ~r1_tarski(A_18, k2_zfmisc_1(A_645, B_646)))), inference(resolution, [status(thm)], [c_32, c_11041])).
% 13.97/5.80  tff(c_30863, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30837, c_11055])).
% 13.97/5.80  tff(c_30899, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11996, c_30863])).
% 13.97/5.80  tff(c_12720, plain, (![B_735, A_18, A_737]: (k1_xboole_0=B_735 | v1_funct_2(A_18, A_737, B_735) | k1_relset_1(A_737, B_735, A_18)!=A_737 | ~r1_tarski(A_18, k2_zfmisc_1(A_737, B_735)))), inference(resolution, [status(thm)], [c_32, c_12691])).
% 13.97/5.80  tff(c_30855, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_3', '#skF_5') | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_30837, c_12720])).
% 13.97/5.80  tff(c_30895, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_141, c_30855])).
% 13.97/5.80  tff(c_31161, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30899, c_30895])).
% 13.97/5.80  tff(c_14334, plain, (![D_840, A_841, B_842]: (m1_subset_1(D_840, k1_zfmisc_1(k2_zfmisc_1(A_841, B_842))) | ~r1_tarski(k2_relat_1(D_840), B_842) | ~m1_subset_1(D_840, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_12237])).
% 13.97/5.80  tff(c_26756, plain, (![D_1256, A_1257, B_1258]: (r1_tarski(D_1256, k2_zfmisc_1(A_1257, B_1258)) | ~r1_tarski(k2_relat_1(D_1256), B_1258) | ~m1_subset_1(D_1256, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_14334, c_30])).
% 13.97/5.80  tff(c_26864, plain, (![A_1257]: (r1_tarski('#skF_6', k2_zfmisc_1(A_1257, '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_10448, c_26756])).
% 13.97/5.80  tff(c_26939, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_26864])).
% 13.97/5.80  tff(c_30441, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_30409])).
% 13.97/5.80  tff(c_30455, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26939, c_30441])).
% 13.97/5.80  tff(c_30467, plain, (~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_30455])).
% 13.97/5.80  tff(c_30482, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_30467])).
% 13.97/5.80  tff(c_31162, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31161, c_30482])).
% 13.97/5.80  tff(c_31324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10505, c_31162])).
% 13.97/5.80  tff(c_31326, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_26864])).
% 13.97/5.80  tff(c_31368, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_31326, c_30])).
% 13.97/5.80  tff(c_10196, plain, (![C_550]: (v1_relat_1(C_550) | ~m1_subset_1(C_550, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_154])).
% 13.97/5.80  tff(c_10202, plain, (![A_551]: (v1_relat_1(A_551) | ~r1_tarski(A_551, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_10196])).
% 13.97/5.80  tff(c_10212, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_10202])).
% 13.97/5.80  tff(c_10577, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_77])).
% 13.97/5.80  tff(c_10580, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_10577])).
% 13.97/5.80  tff(c_10584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_10580])).
% 13.97/5.80  tff(c_10586, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_77])).
% 13.97/5.80  tff(c_10388, plain, (![C_578, B_17]: (v5_relat_1(C_578, B_17) | ~m1_subset_1(C_578, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10378])).
% 13.97/5.80  tff(c_10598, plain, (![B_17]: (v5_relat_1(k1_xboole_0, B_17))), inference(resolution, [status(thm)], [c_10586, c_10388])).
% 13.97/5.80  tff(c_10605, plain, (![B_610]: (v5_relat_1(k1_xboole_0, B_610))), inference(resolution, [status(thm)], [c_10586, c_10388])).
% 13.97/5.80  tff(c_10324, plain, (![B_571, A_572]: (r1_tarski(k2_relat_1(B_571), A_572) | ~v5_relat_1(B_571, A_572) | ~v1_relat_1(B_571))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.97/5.80  tff(c_10357, plain, (![B_571]: (k2_relat_1(B_571)=k1_xboole_0 | ~v5_relat_1(B_571, k1_xboole_0) | ~v1_relat_1(B_571))), inference(resolution, [status(thm)], [c_10324, c_22])).
% 13.97/5.80  tff(c_10611, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10605, c_10357])).
% 13.97/5.80  tff(c_10617, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10212, c_10611])).
% 13.97/5.80  tff(c_10639, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20) | ~v5_relat_1(k1_xboole_0, A_20) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10617, c_36])).
% 13.97/5.80  tff(c_10655, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_10212, c_10598, c_10639])).
% 13.97/5.80  tff(c_10219, plain, (![C_553, B_554, A_555]: (r2_hidden(C_553, B_554) | ~r2_hidden(C_553, A_555) | ~r1_tarski(A_555, B_554))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.97/5.80  tff(c_10860, plain, (![A_633, B_634]: (r2_hidden('#skF_1'(A_633), B_634) | ~r1_tarski(A_633, B_634) | v1_xboole_0(A_633))), inference(resolution, [status(thm)], [c_4, c_10219])).
% 13.97/5.80  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.97/5.80  tff(c_21547, plain, (![A_1148, B_1149, B_1150]: (r2_hidden('#skF_1'(A_1148), B_1149) | ~r1_tarski(B_1150, B_1149) | ~r1_tarski(A_1148, B_1150) | v1_xboole_0(A_1148))), inference(resolution, [status(thm)], [c_10860, c_6])).
% 13.97/5.80  tff(c_21661, plain, (![A_1152, A_1153]: (r2_hidden('#skF_1'(A_1152), A_1153) | ~r1_tarski(A_1152, k1_xboole_0) | v1_xboole_0(A_1152))), inference(resolution, [status(thm)], [c_10655, c_21547])).
% 13.97/5.80  tff(c_21668, plain, (![A_1153, A_1152]: (~v1_xboole_0(A_1153) | ~r1_tarski(A_1152, k1_xboole_0) | v1_xboole_0(A_1152))), inference(resolution, [status(thm)], [c_21661, c_2])).
% 13.97/5.80  tff(c_21669, plain, (![A_1153]: (~v1_xboole_0(A_1153))), inference(splitLeft, [status(thm)], [c_21668])).
% 13.97/5.80  tff(c_21798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21669, c_12])).
% 13.97/5.80  tff(c_21799, plain, (![A_1152]: (~r1_tarski(A_1152, k1_xboole_0) | v1_xboole_0(A_1152))), inference(splitRight, [status(thm)], [c_21668])).
% 13.97/5.80  tff(c_31554, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_31368, c_21799])).
% 13.97/5.80  tff(c_31595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23352, c_31554])).
% 13.97/5.80  tff(c_31597, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_23351])).
% 13.97/5.80  tff(c_31634, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_31597, c_191])).
% 13.97/5.80  tff(c_31658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10187, c_31634])).
% 13.97/5.80  tff(c_31659, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10170])).
% 13.97/5.80  tff(c_31660, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_10170])).
% 13.97/5.80  tff(c_31679, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31659, c_31660])).
% 13.97/5.80  tff(c_31680, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31679, c_31679, c_10160])).
% 13.97/5.80  tff(c_31664, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31659, c_31659, c_28])).
% 13.97/5.80  tff(c_32382, plain, (![A_1440, B_1441, C_1442]: (k1_relset_1(A_1440, B_1441, C_1442)=k1_relat_1(C_1442) | ~m1_subset_1(C_1442, k1_zfmisc_1(k2_zfmisc_1(A_1440, B_1441))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.97/5.80  tff(c_33274, plain, (![B_1506, C_1507]: (k1_relset_1('#skF_3', B_1506, C_1507)=k1_relat_1(C_1507) | ~m1_subset_1(C_1507, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_31664, c_32382])).
% 13.97/5.80  tff(c_33285, plain, (![B_1506]: (k1_relset_1('#skF_3', B_1506, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_31680, c_33274])).
% 13.97/5.80  tff(c_76, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_54])).
% 13.97/5.80  tff(c_32805, plain, (![C_1471, B_1472]: (v1_funct_2(C_1471, '#skF_3', B_1472) | k1_relset_1('#skF_3', B_1472, C_1471)!='#skF_3' | ~m1_subset_1(C_1471, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31659, c_31659, c_31659, c_31659, c_76])).
% 13.97/5.80  tff(c_32968, plain, (![B_1480]: (v1_funct_2('#skF_3', '#skF_3', B_1480) | k1_relset_1('#skF_3', B_1480, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_31680, c_32805])).
% 13.97/5.80  tff(c_31683, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31679, c_141])).
% 13.97/5.80  tff(c_32984, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_32968, c_31683])).
% 13.97/5.80  tff(c_33288, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33285, c_32984])).
% 13.97/5.80  tff(c_31684, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31679, c_70])).
% 13.97/5.80  tff(c_58, plain, (![B_39, C_40]: (k1_relset_1(k1_xboole_0, B_39, C_40)=k1_xboole_0 | ~v1_funct_2(C_40, k1_xboole_0, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.97/5.80  tff(c_75, plain, (![B_39, C_40]: (k1_relset_1(k1_xboole_0, B_39, C_40)=k1_xboole_0 | ~v1_funct_2(C_40, k1_xboole_0, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_58])).
% 13.97/5.80  tff(c_32580, plain, (![B_1456, C_1457]: (k1_relset_1('#skF_3', B_1456, C_1457)='#skF_3' | ~v1_funct_2(C_1457, '#skF_3', B_1456) | ~m1_subset_1(C_1457, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31659, c_31659, c_31659, c_31659, c_75])).
% 13.97/5.80  tff(c_32585, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_31684, c_32580])).
% 13.97/5.80  tff(c_32592, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31680, c_32585])).
% 13.97/5.80  tff(c_33290, plain, (![B_1508]: (k1_relset_1('#skF_3', B_1508, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_31680, c_33274])).
% 13.97/5.80  tff(c_33304, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_32592, c_33290])).
% 13.97/5.80  tff(c_33311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33288, c_33304])).
% 13.97/5.80  tff(c_33312, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_74])).
% 13.97/5.80  tff(c_35124, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_35092, c_33312])).
% 13.97/5.80  tff(c_35131, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_35124])).
% 13.97/5.80  tff(c_35143, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_33332, c_35131])).
% 13.97/5.80  tff(c_35148, plain, (~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_33712, c_35143])).
% 13.97/5.80  tff(c_35158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33332, c_33625, c_35148])).
% 13.97/5.80  tff(c_35160, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 13.97/5.80  tff(c_35177, plain, (![B_17]: (k2_zfmisc_1('#skF_4', B_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35160, c_35160, c_28])).
% 13.97/5.80  tff(c_35159, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 13.97/5.80  tff(c_35166, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35160, c_35159])).
% 13.97/5.80  tff(c_35201, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35177, c_35166, c_68])).
% 13.97/5.80  tff(c_35217, plain, (![A_1687, B_1688]: (r1_tarski(A_1687, B_1688) | ~m1_subset_1(A_1687, k1_zfmisc_1(B_1688)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.97/5.80  tff(c_35225, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_35201, c_35217])).
% 13.97/5.80  tff(c_35202, plain, (![A_15]: (A_15='#skF_4' | ~r1_tarski(A_15, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35160, c_35160, c_22])).
% 13.97/5.80  tff(c_35229, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_35225, c_35202])).
% 13.97/5.80  tff(c_35232, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35229, c_35201])).
% 13.97/5.80  tff(c_36230, plain, (![A_1815, B_1816, C_1817]: (k1_relset_1(A_1815, B_1816, C_1817)=k1_relat_1(C_1817) | ~m1_subset_1(C_1817, k1_zfmisc_1(k2_zfmisc_1(A_1815, B_1816))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.97/5.80  tff(c_36392, plain, (![B_1822, C_1823]: (k1_relset_1('#skF_4', B_1822, C_1823)=k1_relat_1(C_1823) | ~m1_subset_1(C_1823, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_35177, c_36230])).
% 13.97/5.80  tff(c_36398, plain, (![B_1822]: (k1_relset_1('#skF_4', B_1822, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_35232, c_36392])).
% 13.97/5.80  tff(c_36401, plain, (![C_1824, B_1825]: (v1_funct_2(C_1824, '#skF_4', B_1825) | k1_relset_1('#skF_4', B_1825, C_1824)!='#skF_4' | ~m1_subset_1(C_1824, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35160, c_35160, c_35160, c_35160, c_76])).
% 13.97/5.80  tff(c_36407, plain, (![B_1825]: (v1_funct_2('#skF_4', '#skF_4', B_1825) | k1_relset_1('#skF_4', B_1825, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_35232, c_36401])).
% 13.97/5.80  tff(c_36453, plain, (![B_1825]: (v1_funct_2('#skF_4', '#skF_4', B_1825) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36398, c_36407])).
% 13.97/5.80  tff(c_36454, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36453])).
% 13.97/5.80  tff(c_35172, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35166, c_70])).
% 13.97/5.80  tff(c_35231, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35229, c_35172])).
% 13.97/5.80  tff(c_36516, plain, (![B_1838, C_1839]: (k1_relset_1('#skF_4', B_1838, C_1839)='#skF_4' | ~v1_funct_2(C_1839, '#skF_4', B_1838) | ~m1_subset_1(C_1839, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35160, c_35160, c_35160, c_35160, c_75])).
% 13.97/5.80  tff(c_36521, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_35231, c_36516])).
% 13.97/5.80  tff(c_36529, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35232, c_36398, c_36521])).
% 13.97/5.80  tff(c_36531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36454, c_36529])).
% 13.97/5.80  tff(c_36532, plain, (![B_1825]: (v1_funct_2('#skF_4', '#skF_4', B_1825))), inference(splitRight, [status(thm)], [c_36453])).
% 13.97/5.80  tff(c_35239, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35229, c_35166, c_35229, c_35177, c_35166, c_74])).
% 13.97/5.80  tff(c_35240, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_35239])).
% 13.97/5.80  tff(c_36542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36532, c_35240])).
% 13.97/5.80  tff(c_36543, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_35239])).
% 13.97/5.80  tff(c_36551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35232, c_36543])).
% 13.97/5.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/5.80  
% 13.97/5.80  Inference rules
% 13.97/5.80  ----------------------
% 13.97/5.80  #Ref     : 0
% 13.97/5.80  #Sup     : 7963
% 13.97/5.80  #Fact    : 0
% 13.97/5.80  #Define  : 0
% 13.97/5.80  #Split   : 108
% 13.97/5.80  #Chain   : 0
% 13.97/5.80  #Close   : 0
% 13.97/5.80  
% 13.97/5.80  Ordering : KBO
% 13.97/5.80  
% 13.97/5.80  Simplification rules
% 13.97/5.80  ----------------------
% 13.97/5.80  #Subsume      : 2635
% 13.97/5.80  #Demod        : 6954
% 13.97/5.80  #Tautology    : 2914
% 13.97/5.80  #SimpNegUnit  : 250
% 13.97/5.80  #BackRed      : 802
% 13.97/5.80  
% 13.97/5.80  #Partial instantiations: 0
% 13.97/5.80  #Strategies tried      : 1
% 13.97/5.80  
% 13.97/5.80  Timing (in seconds)
% 13.97/5.80  ----------------------
% 13.97/5.80  Preprocessing        : 0.42
% 13.97/5.80  Parsing              : 0.21
% 13.97/5.80  CNF conversion       : 0.03
% 13.97/5.80  Main loop            : 4.45
% 13.97/5.80  Inferencing          : 1.13
% 13.97/5.80  Reduction            : 1.67
% 13.97/5.80  Demodulation         : 1.20
% 13.97/5.80  BG Simplification    : 0.10
% 13.97/5.80  Subsumption          : 1.23
% 13.97/5.80  Abstraction          : 0.14
% 13.97/5.80  MUC search           : 0.00
% 13.97/5.80  Cooper               : 0.00
% 13.97/5.80  Total                : 4.99
% 13.97/5.80  Index Insertion      : 0.00
% 13.97/5.80  Index Deletion       : 0.00
% 13.97/5.80  Index Matching       : 0.00
% 13.97/5.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
