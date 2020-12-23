%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 23.35s
% Output     : CNFRefutation 23.78s
% Verified   : 
% Statistics : Number of formulae       :  192 (1662 expanded)
%              Number of leaves         :   41 ( 521 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 (4918 expanded)
%              Number of equality atoms :   83 (1599 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_105,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_105])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_74680,plain,(
    ! [A_1601,B_1602,C_1603] :
      ( k1_relset_1(A_1601,B_1602,C_1603) = k1_relat_1(C_1603)
      | ~ m1_subset_1(C_1603,k1_zfmisc_1(k2_zfmisc_1(A_1601,B_1602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74692,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_74680])).

tff(c_74994,plain,(
    ! [B_1646,A_1647,C_1648] :
      ( k1_xboole_0 = B_1646
      | k1_relset_1(A_1647,B_1646,C_1648) = A_1647
      | ~ v1_funct_2(C_1648,A_1647,B_1646)
      | ~ m1_subset_1(C_1648,k1_zfmisc_1(k2_zfmisc_1(A_1647,B_1646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75003,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_74994])).

tff(c_75014,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74692,c_75003])).

tff(c_75015,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_75014])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75034,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75015,c_26])).

tff(c_75092,plain,(
    ! [A_1651] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1651)) = A_1651
      | ~ r1_tarski(A_1651,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_75034])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_74876,plain,(
    ! [A_1631,B_1632,C_1633,D_1634] :
      ( k2_partfun1(A_1631,B_1632,C_1633,D_1634) = k7_relat_1(C_1633,D_1634)
      | ~ m1_subset_1(C_1633,k1_zfmisc_1(k2_zfmisc_1(A_1631,B_1632)))
      | ~ v1_funct_1(C_1633) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74882,plain,(
    ! [D_1634] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1634) = k7_relat_1('#skF_4',D_1634)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_74876])).

tff(c_74892,plain,(
    ! [D_1634] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1634) = k7_relat_1('#skF_4',D_1634) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74882])).

tff(c_2206,plain,(
    ! [A_308,B_309,C_310,D_311] :
      ( k2_partfun1(A_308,B_309,C_310,D_311) = k7_relat_1(C_310,D_311)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309)))
      | ~ v1_funct_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2210,plain,(
    ! [D_311] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_311) = k7_relat_1('#skF_4',D_311)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_2206])).

tff(c_2217,plain,(
    ! [D_311] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_311) = k7_relat_1('#skF_4',D_311) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2210])).

tff(c_2573,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( m1_subset_1(k2_partfun1(A_336,B_337,C_338,D_339),k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ v1_funct_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2615,plain,(
    ! [D_311] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_311),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2217,c_2573])).

tff(c_2640,plain,(
    ! [D_340] : m1_subset_1(k7_relat_1('#skF_4',D_340),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2615])).

tff(c_28,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2685,plain,(
    ! [D_340] : v1_relat_1(k7_relat_1('#skF_4',D_340)) ),
    inference(resolution,[status(thm)],[c_2640,c_28])).

tff(c_30,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2684,plain,(
    ! [D_340] : v5_relat_1(k7_relat_1('#skF_4',D_340),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2640,c_30])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2021,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( v1_funct_1(k2_partfun1(A_283,B_284,C_285,D_286))
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2023,plain,(
    ! [D_286] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_286))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_2021])).

tff(c_2029,plain,(
    ! [D_286] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2023])).

tff(c_2230,plain,(
    ! [D_286] : v1_funct_1(k7_relat_1('#skF_4',D_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_2029])).

tff(c_549,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_557,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_549])).

tff(c_2256,plain,(
    ! [B_319,A_320,C_321] :
      ( k1_xboole_0 = B_319
      | k1_relset_1(A_320,B_319,C_321) = A_320
      | ~ v1_funct_2(C_321,A_320,B_319)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2256])).

tff(c_2270,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_557,c_2262])).

tff(c_2271,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2270])).

tff(c_2290,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2271,c_26])).

tff(c_2334,plain,(
    ! [A_322] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_322)) = A_322
      | ~ r1_tarski(A_322,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2290])).

tff(c_56,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42),A_41)))
      | ~ r1_tarski(k2_relat_1(B_42),A_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2346,plain,(
    ! [A_322,A_41] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_322),k1_zfmisc_1(k2_zfmisc_1(A_322,A_41)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_322)),A_41)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_322))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_322))
      | ~ r1_tarski(A_322,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2334,c_56])).

tff(c_2385,plain,(
    ! [A_322,A_41] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_322),k1_zfmisc_1(k2_zfmisc_1(A_322,A_41)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_322)),A_41)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_322))
      | ~ r1_tarski(A_322,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_2346])).

tff(c_74335,plain,(
    ! [A_1572,A_1573] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1572),k1_zfmisc_1(k2_zfmisc_1(A_1572,A_1573)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1572)),A_1573)
      | ~ r1_tarski(A_1572,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2385])).

tff(c_404,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( v1_funct_1(k2_partfun1(A_97,B_98,C_99,D_100))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_406,plain,(
    ! [D_100] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_100))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_404])).

tff(c_412,plain,(
    ! [D_100] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_406])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_135,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_135])).

tff(c_417,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_437,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_2231,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_437])).

tff(c_74376,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74335,c_2231])).

tff(c_74453,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74376])).

tff(c_74481,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_74453])).

tff(c_74487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2684,c_74481])).

tff(c_74489,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_74691,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74489,c_74680])).

tff(c_74895,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74892,c_74892,c_74691])).

tff(c_74488,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_74903,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74892,c_74488])).

tff(c_74902,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74892,c_74489])).

tff(c_74952,plain,(
    ! [B_1639,C_1640,A_1641] :
      ( k1_xboole_0 = B_1639
      | v1_funct_2(C_1640,A_1641,B_1639)
      | k1_relset_1(A_1641,B_1639,C_1640) != A_1641
      | ~ m1_subset_1(C_1640,k1_zfmisc_1(k2_zfmisc_1(A_1641,B_1639))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74955,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_74902,c_74952])).

tff(c_74968,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_74903,c_79,c_74955])).

tff(c_74977,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74895,c_74968])).

tff(c_75101,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75092,c_74977])).

tff(c_75146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_75101])).

tff(c_75147,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_75148,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_75156,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75147,c_75148])).

tff(c_75171,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75156,c_68])).

tff(c_75176,plain,(
    ! [C_1660,A_1661,B_1662] :
      ( v1_relat_1(C_1660)
      | ~ m1_subset_1(C_1660,k1_zfmisc_1(k2_zfmisc_1(A_1661,B_1662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75184,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75171,c_75176])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_75151,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75147,c_2])).

tff(c_76397,plain,(
    ! [C_1802,A_1803,B_1804] :
      ( v1_xboole_0(C_1802)
      | ~ m1_subset_1(C_1802,k1_zfmisc_1(k2_zfmisc_1(A_1803,B_1804)))
      | ~ v1_xboole_0(A_1803) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76400,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_75171,c_76397])).

tff(c_76407,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75151,c_76400])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75163,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75147,c_4])).

tff(c_76413,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76407,c_75163])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75150,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75147,c_12])).

tff(c_76431,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_75150])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75149,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75147,c_14])).

tff(c_75185,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_75149,c_75176])).

tff(c_75772,plain,(
    ! [C_1734,B_1735,A_1736] :
      ( v5_relat_1(C_1734,B_1735)
      | ~ m1_subset_1(C_1734,k1_zfmisc_1(k2_zfmisc_1(A_1736,B_1735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76342,plain,(
    ! [B_1800] : v5_relat_1('#skF_1',B_1800) ),
    inference(resolution,[status(thm)],[c_75149,c_75772])).

tff(c_75748,plain,(
    ! [B_1728,A_1729] :
      ( r1_tarski(k2_relat_1(B_1728),A_1729)
      | ~ v5_relat_1(B_1728,A_1729)
      | ~ v1_relat_1(B_1728) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75186,plain,(
    ! [B_1663,A_1664] :
      ( B_1663 = A_1664
      | ~ r1_tarski(B_1663,A_1664)
      | ~ r1_tarski(A_1664,B_1663) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75196,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_75150,c_75186])).

tff(c_75759,plain,(
    ! [B_1728] :
      ( k2_relat_1(B_1728) = '#skF_1'
      | ~ v5_relat_1(B_1728,'#skF_1')
      | ~ v1_relat_1(B_1728) ) ),
    inference(resolution,[status(thm)],[c_75748,c_75196])).

tff(c_76346,plain,
    ( k2_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_76342,c_75759])).

tff(c_76349,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75185,c_76346])).

tff(c_76414,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_76413,c_76349])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75704,plain,(
    ! [A_1723] :
      ( A_1723 = '#skF_1'
      | ~ r1_tarski(A_1723,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_75150,c_75186])).

tff(c_75708,plain,(
    ! [A_13] :
      ( k7_relat_1('#skF_1',A_13) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_75704])).

tff(c_75719,plain,(
    ! [A_13] : k7_relat_1('#skF_1',A_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75185,c_75708])).

tff(c_76422,plain,(
    ! [A_13] : k7_relat_1('#skF_4',A_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_76413,c_75719])).

tff(c_76481,plain,(
    ! [B_1810,A_1811] :
      ( k1_relat_1(k7_relat_1(B_1810,A_1811)) = A_1811
      | ~ r1_tarski(A_1811,k1_relat_1(B_1810))
      | ~ v1_relat_1(B_1810) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76594,plain,(
    ! [B_1824] :
      ( k1_relat_1(k7_relat_1(B_1824,'#skF_4')) = '#skF_4'
      | ~ v1_relat_1(B_1824) ) ),
    inference(resolution,[status(thm)],[c_76431,c_76481])).

tff(c_76607,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76422,c_76594])).

tff(c_76611,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75184,c_76607])).

tff(c_76672,plain,(
    ! [B_1827,A_1828] :
      ( v1_funct_2(B_1827,k1_relat_1(B_1827),A_1828)
      | ~ r1_tarski(k2_relat_1(B_1827),A_1828)
      | ~ v1_funct_1(B_1827)
      | ~ v1_relat_1(B_1827) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76675,plain,(
    ! [A_1828] :
      ( v1_funct_2('#skF_4','#skF_4',A_1828)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1828)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76611,c_76672])).

tff(c_76680,plain,(
    ! [A_1828] : v1_funct_2('#skF_4','#skF_4',A_1828) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75184,c_72,c_76431,c_76414,c_76675])).

tff(c_75852,plain,(
    ! [C_1743,A_1744,B_1745] :
      ( v1_xboole_0(C_1743)
      | ~ m1_subset_1(C_1743,k1_zfmisc_1(k2_zfmisc_1(A_1744,B_1745)))
      | ~ v1_xboole_0(A_1744) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75855,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_75171,c_75852])).

tff(c_75862,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75151,c_75855])).

tff(c_75868,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_75862,c_75163])).

tff(c_75883,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75868,c_75149])).

tff(c_75876,plain,(
    ! [A_13] : k7_relat_1('#skF_4',A_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75868,c_75868,c_75719])).

tff(c_76324,plain,(
    ! [A_1796,B_1797,C_1798,D_1799] :
      ( k2_partfun1(A_1796,B_1797,C_1798,D_1799) = k7_relat_1(C_1798,D_1799)
      | ~ m1_subset_1(C_1798,k1_zfmisc_1(k2_zfmisc_1(A_1796,B_1797)))
      | ~ v1_funct_1(C_1798) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_76329,plain,(
    ! [A_1796,B_1797,D_1799] :
      ( k2_partfun1(A_1796,B_1797,'#skF_4',D_1799) = k7_relat_1('#skF_4',D_1799)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_75883,c_76324])).

tff(c_76333,plain,(
    ! [A_1796,B_1797,D_1799] : k2_partfun1(A_1796,B_1797,'#skF_4',D_1799) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_75876,c_76329])).

tff(c_75361,plain,(
    ! [C_1688,A_1689,B_1690] :
      ( v1_xboole_0(C_1688)
      | ~ m1_subset_1(C_1688,k1_zfmisc_1(k2_zfmisc_1(A_1689,B_1690)))
      | ~ v1_xboole_0(A_1689) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75364,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_75171,c_75361])).

tff(c_75371,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75151,c_75364])).

tff(c_75377,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_75371,c_75163])).

tff(c_75394,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75377,c_75149])).

tff(c_75692,plain,(
    ! [A_1719,B_1720,C_1721,D_1722] :
      ( v1_funct_1(k2_partfun1(A_1719,B_1720,C_1721,D_1722))
      | ~ m1_subset_1(C_1721,k1_zfmisc_1(k2_zfmisc_1(A_1719,B_1720)))
      | ~ v1_funct_1(C_1721) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75695,plain,(
    ! [A_1719,B_1720,D_1722] :
      ( v1_funct_1(k2_partfun1(A_1719,B_1720,'#skF_4',D_1722))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_75394,c_75692])).

tff(c_75698,plain,(
    ! [A_1719,B_1720,D_1722] : v1_funct_1(k2_partfun1(A_1719,B_1720,'#skF_4',D_1722)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_75695])).

tff(c_75194,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_75186])).

tff(c_75203,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75150,c_75194])).

tff(c_75210,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75203,c_75156,c_75203,c_75203,c_75156,c_75156,c_75203,c_75203,c_75156,c_75156,c_62])).

tff(c_75211,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_75210])).

tff(c_75386,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75377,c_75377,c_75377,c_75211])).

tff(c_75701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75698,c_75386])).

tff(c_75702,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_75210])).

tff(c_75789,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_75702])).

tff(c_76138,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75868,c_75868,c_75868,c_75868,c_75868,c_75789])).

tff(c_76335,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76333,c_76138])).

tff(c_76339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75883,c_76335])).

tff(c_76341,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_75702])).

tff(c_76622,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_76413,c_76413,c_76413,c_76413,c_76341])).

tff(c_34,plain,(
    ! [C_26,A_23,B_24] :
      ( v1_xboole_0(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76630,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76622,c_34])).

tff(c_76644,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76407,c_76630])).

tff(c_76430,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_75163])).

tff(c_76658,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76644,c_76430])).

tff(c_76340,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_75702])).

tff(c_76415,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76413,c_76413,c_76413,c_76413,c_76413,c_76340])).

tff(c_76685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76680,c_76658,c_76415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:53:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.35/14.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.35/14.50  
% 23.35/14.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.35/14.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 23.35/14.50  
% 23.35/14.50  %Foreground sorts:
% 23.35/14.50  
% 23.35/14.50  
% 23.35/14.50  %Background operators:
% 23.35/14.50  
% 23.35/14.50  
% 23.35/14.50  %Foreground operators:
% 23.35/14.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.35/14.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.35/14.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.35/14.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.35/14.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.35/14.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.35/14.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.35/14.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.35/14.50  tff('#skF_2', type, '#skF_2': $i).
% 23.35/14.50  tff('#skF_3', type, '#skF_3': $i).
% 23.35/14.50  tff('#skF_1', type, '#skF_1': $i).
% 23.35/14.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 23.35/14.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 23.35/14.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.35/14.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.35/14.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.35/14.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.35/14.50  tff('#skF_4', type, '#skF_4': $i).
% 23.35/14.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.35/14.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 23.35/14.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 23.35/14.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.35/14.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.35/14.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.35/14.50  
% 23.78/14.53  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 23.78/14.53  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.78/14.53  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.78/14.53  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 23.78/14.53  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 23.78/14.53  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 23.78/14.53  tff(f_113, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 23.78/14.53  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.78/14.53  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 23.78/14.53  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 23.78/14.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.78/14.53  tff(f_83, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 23.78/14.53  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 23.78/14.53  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.78/14.53  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 23.78/14.53  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.78/14.53  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 23.78/14.53  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_105, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.78/14.53  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_105])).
% 23.78/14.53  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_79, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 23.78/14.53  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_74680, plain, (![A_1601, B_1602, C_1603]: (k1_relset_1(A_1601, B_1602, C_1603)=k1_relat_1(C_1603) | ~m1_subset_1(C_1603, k1_zfmisc_1(k2_zfmisc_1(A_1601, B_1602))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.78/14.53  tff(c_74692, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_74680])).
% 23.78/14.53  tff(c_74994, plain, (![B_1646, A_1647, C_1648]: (k1_xboole_0=B_1646 | k1_relset_1(A_1647, B_1646, C_1648)=A_1647 | ~v1_funct_2(C_1648, A_1647, B_1646) | ~m1_subset_1(C_1648, k1_zfmisc_1(k2_zfmisc_1(A_1647, B_1646))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.78/14.53  tff(c_75003, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_74994])).
% 23.78/14.53  tff(c_75014, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74692, c_75003])).
% 23.78/14.53  tff(c_75015, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_75014])).
% 23.78/14.53  tff(c_26, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.78/14.53  tff(c_75034, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75015, c_26])).
% 23.78/14.53  tff(c_75092, plain, (![A_1651]: (k1_relat_1(k7_relat_1('#skF_4', A_1651))=A_1651 | ~r1_tarski(A_1651, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_75034])).
% 23.78/14.53  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_74876, plain, (![A_1631, B_1632, C_1633, D_1634]: (k2_partfun1(A_1631, B_1632, C_1633, D_1634)=k7_relat_1(C_1633, D_1634) | ~m1_subset_1(C_1633, k1_zfmisc_1(k2_zfmisc_1(A_1631, B_1632))) | ~v1_funct_1(C_1633))), inference(cnfTransformation, [status(thm)], [f_119])).
% 23.78/14.53  tff(c_74882, plain, (![D_1634]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1634)=k7_relat_1('#skF_4', D_1634) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_74876])).
% 23.78/14.53  tff(c_74892, plain, (![D_1634]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1634)=k7_relat_1('#skF_4', D_1634))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74882])).
% 23.78/14.53  tff(c_2206, plain, (![A_308, B_309, C_310, D_311]: (k2_partfun1(A_308, B_309, C_310, D_311)=k7_relat_1(C_310, D_311) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))) | ~v1_funct_1(C_310))), inference(cnfTransformation, [status(thm)], [f_119])).
% 23.78/14.53  tff(c_2210, plain, (![D_311]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_311)=k7_relat_1('#skF_4', D_311) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2206])).
% 23.78/14.53  tff(c_2217, plain, (![D_311]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_311)=k7_relat_1('#skF_4', D_311))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2210])).
% 23.78/14.53  tff(c_2573, plain, (![A_336, B_337, C_338, D_339]: (m1_subset_1(k2_partfun1(A_336, B_337, C_338, D_339), k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~v1_funct_1(C_338))), inference(cnfTransformation, [status(thm)], [f_113])).
% 23.78/14.53  tff(c_2615, plain, (![D_311]: (m1_subset_1(k7_relat_1('#skF_4', D_311), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2217, c_2573])).
% 23.78/14.53  tff(c_2640, plain, (![D_340]: (m1_subset_1(k7_relat_1('#skF_4', D_340), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2615])).
% 23.78/14.53  tff(c_28, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.78/14.53  tff(c_2685, plain, (![D_340]: (v1_relat_1(k7_relat_1('#skF_4', D_340)))), inference(resolution, [status(thm)], [c_2640, c_28])).
% 23.78/14.53  tff(c_30, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 23.78/14.53  tff(c_2684, plain, (![D_340]: (v5_relat_1(k7_relat_1('#skF_4', D_340), '#skF_2'))), inference(resolution, [status(thm)], [c_2640, c_30])).
% 23.78/14.53  tff(c_20, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.78/14.53  tff(c_2021, plain, (![A_283, B_284, C_285, D_286]: (v1_funct_1(k2_partfun1(A_283, B_284, C_285, D_286)) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_113])).
% 23.78/14.53  tff(c_2023, plain, (![D_286]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_286)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2021])).
% 23.78/14.53  tff(c_2029, plain, (![D_286]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_286)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2023])).
% 23.78/14.53  tff(c_2230, plain, (![D_286]: (v1_funct_1(k7_relat_1('#skF_4', D_286)))), inference(demodulation, [status(thm), theory('equality')], [c_2217, c_2029])).
% 23.78/14.53  tff(c_549, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.78/14.53  tff(c_557, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_549])).
% 23.78/14.53  tff(c_2256, plain, (![B_319, A_320, C_321]: (k1_xboole_0=B_319 | k1_relset_1(A_320, B_319, C_321)=A_320 | ~v1_funct_2(C_321, A_320, B_319) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.78/14.53  tff(c_2262, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_2256])).
% 23.78/14.53  tff(c_2270, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_557, c_2262])).
% 23.78/14.53  tff(c_2271, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_2270])).
% 23.78/14.53  tff(c_2290, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2271, c_26])).
% 23.78/14.53  tff(c_2334, plain, (![A_322]: (k1_relat_1(k7_relat_1('#skF_4', A_322))=A_322 | ~r1_tarski(A_322, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2290])).
% 23.78/14.53  tff(c_56, plain, (![B_42, A_41]: (m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42), A_41))) | ~r1_tarski(k2_relat_1(B_42), A_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.78/14.53  tff(c_2346, plain, (![A_322, A_41]: (m1_subset_1(k7_relat_1('#skF_4', A_322), k1_zfmisc_1(k2_zfmisc_1(A_322, A_41))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_322)), A_41) | ~v1_funct_1(k7_relat_1('#skF_4', A_322)) | ~v1_relat_1(k7_relat_1('#skF_4', A_322)) | ~r1_tarski(A_322, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2334, c_56])).
% 23.78/14.53  tff(c_2385, plain, (![A_322, A_41]: (m1_subset_1(k7_relat_1('#skF_4', A_322), k1_zfmisc_1(k2_zfmisc_1(A_322, A_41))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_322)), A_41) | ~v1_relat_1(k7_relat_1('#skF_4', A_322)) | ~r1_tarski(A_322, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_2346])).
% 23.78/14.53  tff(c_74335, plain, (![A_1572, A_1573]: (m1_subset_1(k7_relat_1('#skF_4', A_1572), k1_zfmisc_1(k2_zfmisc_1(A_1572, A_1573))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1572)), A_1573) | ~r1_tarski(A_1572, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2385])).
% 23.78/14.53  tff(c_404, plain, (![A_97, B_98, C_99, D_100]: (v1_funct_1(k2_partfun1(A_97, B_98, C_99, D_100)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_113])).
% 23.78/14.53  tff(c_406, plain, (![D_100]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_100)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_404])).
% 23.78/14.53  tff(c_412, plain, (![D_100]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_100)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_406])).
% 23.78/14.53  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.78/14.53  tff(c_135, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 23.78/14.53  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_135])).
% 23.78/14.53  tff(c_417, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 23.78/14.53  tff(c_437, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_417])).
% 23.78/14.53  tff(c_2231, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2217, c_437])).
% 23.78/14.53  tff(c_74376, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74335, c_2231])).
% 23.78/14.53  tff(c_74453, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74376])).
% 23.78/14.53  tff(c_74481, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_74453])).
% 23.78/14.53  tff(c_74487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2684, c_74481])).
% 23.78/14.53  tff(c_74489, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_417])).
% 23.78/14.53  tff(c_74691, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_74489, c_74680])).
% 23.78/14.53  tff(c_74895, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74892, c_74892, c_74691])).
% 23.78/14.53  tff(c_74488, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_417])).
% 23.78/14.53  tff(c_74903, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74892, c_74488])).
% 23.78/14.53  tff(c_74902, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74892, c_74489])).
% 23.78/14.53  tff(c_74952, plain, (![B_1639, C_1640, A_1641]: (k1_xboole_0=B_1639 | v1_funct_2(C_1640, A_1641, B_1639) | k1_relset_1(A_1641, B_1639, C_1640)!=A_1641 | ~m1_subset_1(C_1640, k1_zfmisc_1(k2_zfmisc_1(A_1641, B_1639))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.78/14.53  tff(c_74955, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_74902, c_74952])).
% 23.78/14.53  tff(c_74968, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_74903, c_79, c_74955])).
% 23.78/14.53  tff(c_74977, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74895, c_74968])).
% 23.78/14.53  tff(c_75101, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75092, c_74977])).
% 23.78/14.53  tff(c_75146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_75101])).
% 23.78/14.53  tff(c_75147, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 23.78/14.53  tff(c_75148, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 23.78/14.53  tff(c_75156, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75147, c_75148])).
% 23.78/14.53  tff(c_75171, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_75156, c_68])).
% 23.78/14.53  tff(c_75176, plain, (![C_1660, A_1661, B_1662]: (v1_relat_1(C_1660) | ~m1_subset_1(C_1660, k1_zfmisc_1(k2_zfmisc_1(A_1661, B_1662))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.78/14.53  tff(c_75184, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75171, c_75176])).
% 23.78/14.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.78/14.53  tff(c_75151, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_75147, c_2])).
% 23.78/14.53  tff(c_76397, plain, (![C_1802, A_1803, B_1804]: (v1_xboole_0(C_1802) | ~m1_subset_1(C_1802, k1_zfmisc_1(k2_zfmisc_1(A_1803, B_1804))) | ~v1_xboole_0(A_1803))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.78/14.53  tff(c_76400, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_75171, c_76397])).
% 23.78/14.53  tff(c_76407, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75151, c_76400])).
% 23.78/14.53  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 23.78/14.53  tff(c_75163, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_75147, c_4])).
% 23.78/14.53  tff(c_76413, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_76407, c_75163])).
% 23.78/14.53  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 23.78/14.53  tff(c_75150, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_75147, c_12])).
% 23.78/14.53  tff(c_76431, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_75150])).
% 23.78/14.53  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.78/14.53  tff(c_75149, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_75147, c_14])).
% 23.78/14.53  tff(c_75185, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_75149, c_75176])).
% 23.78/14.53  tff(c_75772, plain, (![C_1734, B_1735, A_1736]: (v5_relat_1(C_1734, B_1735) | ~m1_subset_1(C_1734, k1_zfmisc_1(k2_zfmisc_1(A_1736, B_1735))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 23.78/14.53  tff(c_76342, plain, (![B_1800]: (v5_relat_1('#skF_1', B_1800))), inference(resolution, [status(thm)], [c_75149, c_75772])).
% 23.78/14.53  tff(c_75748, plain, (![B_1728, A_1729]: (r1_tarski(k2_relat_1(B_1728), A_1729) | ~v5_relat_1(B_1728, A_1729) | ~v1_relat_1(B_1728))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.78/14.53  tff(c_75186, plain, (![B_1663, A_1664]: (B_1663=A_1664 | ~r1_tarski(B_1663, A_1664) | ~r1_tarski(A_1664, B_1663))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.78/14.53  tff(c_75196, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_75150, c_75186])).
% 23.78/14.53  tff(c_75759, plain, (![B_1728]: (k2_relat_1(B_1728)='#skF_1' | ~v5_relat_1(B_1728, '#skF_1') | ~v1_relat_1(B_1728))), inference(resolution, [status(thm)], [c_75748, c_75196])).
% 23.78/14.53  tff(c_76346, plain, (k2_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_76342, c_75759])).
% 23.78/14.53  tff(c_76349, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75185, c_76346])).
% 23.78/14.53  tff(c_76414, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_76413, c_76349])).
% 23.78/14.53  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 23.78/14.53  tff(c_75704, plain, (![A_1723]: (A_1723='#skF_1' | ~r1_tarski(A_1723, '#skF_1'))), inference(resolution, [status(thm)], [c_75150, c_75186])).
% 23.78/14.53  tff(c_75708, plain, (![A_13]: (k7_relat_1('#skF_1', A_13)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_75704])).
% 23.78/14.53  tff(c_75719, plain, (![A_13]: (k7_relat_1('#skF_1', A_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_75185, c_75708])).
% 23.78/14.53  tff(c_76422, plain, (![A_13]: (k7_relat_1('#skF_4', A_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_76413, c_75719])).
% 23.78/14.53  tff(c_76481, plain, (![B_1810, A_1811]: (k1_relat_1(k7_relat_1(B_1810, A_1811))=A_1811 | ~r1_tarski(A_1811, k1_relat_1(B_1810)) | ~v1_relat_1(B_1810))), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.78/14.53  tff(c_76594, plain, (![B_1824]: (k1_relat_1(k7_relat_1(B_1824, '#skF_4'))='#skF_4' | ~v1_relat_1(B_1824))), inference(resolution, [status(thm)], [c_76431, c_76481])).
% 23.78/14.53  tff(c_76607, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76422, c_76594])).
% 23.78/14.53  tff(c_76611, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75184, c_76607])).
% 23.78/14.53  tff(c_76672, plain, (![B_1827, A_1828]: (v1_funct_2(B_1827, k1_relat_1(B_1827), A_1828) | ~r1_tarski(k2_relat_1(B_1827), A_1828) | ~v1_funct_1(B_1827) | ~v1_relat_1(B_1827))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.78/14.53  tff(c_76675, plain, (![A_1828]: (v1_funct_2('#skF_4', '#skF_4', A_1828) | ~r1_tarski(k2_relat_1('#skF_4'), A_1828) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76611, c_76672])).
% 23.78/14.53  tff(c_76680, plain, (![A_1828]: (v1_funct_2('#skF_4', '#skF_4', A_1828))), inference(demodulation, [status(thm), theory('equality')], [c_75184, c_72, c_76431, c_76414, c_76675])).
% 23.78/14.53  tff(c_75852, plain, (![C_1743, A_1744, B_1745]: (v1_xboole_0(C_1743) | ~m1_subset_1(C_1743, k1_zfmisc_1(k2_zfmisc_1(A_1744, B_1745))) | ~v1_xboole_0(A_1744))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.78/14.53  tff(c_75855, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_75171, c_75852])).
% 23.78/14.53  tff(c_75862, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75151, c_75855])).
% 23.78/14.53  tff(c_75868, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_75862, c_75163])).
% 23.78/14.53  tff(c_75883, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_75868, c_75149])).
% 23.78/14.53  tff(c_75876, plain, (![A_13]: (k7_relat_1('#skF_4', A_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75868, c_75868, c_75719])).
% 23.78/14.53  tff(c_76324, plain, (![A_1796, B_1797, C_1798, D_1799]: (k2_partfun1(A_1796, B_1797, C_1798, D_1799)=k7_relat_1(C_1798, D_1799) | ~m1_subset_1(C_1798, k1_zfmisc_1(k2_zfmisc_1(A_1796, B_1797))) | ~v1_funct_1(C_1798))), inference(cnfTransformation, [status(thm)], [f_119])).
% 23.78/14.53  tff(c_76329, plain, (![A_1796, B_1797, D_1799]: (k2_partfun1(A_1796, B_1797, '#skF_4', D_1799)=k7_relat_1('#skF_4', D_1799) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_75883, c_76324])).
% 23.78/14.53  tff(c_76333, plain, (![A_1796, B_1797, D_1799]: (k2_partfun1(A_1796, B_1797, '#skF_4', D_1799)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_75876, c_76329])).
% 23.78/14.53  tff(c_75361, plain, (![C_1688, A_1689, B_1690]: (v1_xboole_0(C_1688) | ~m1_subset_1(C_1688, k1_zfmisc_1(k2_zfmisc_1(A_1689, B_1690))) | ~v1_xboole_0(A_1689))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.78/14.53  tff(c_75364, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_75171, c_75361])).
% 23.78/14.53  tff(c_75371, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75151, c_75364])).
% 23.78/14.53  tff(c_75377, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_75371, c_75163])).
% 23.78/14.53  tff(c_75394, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_75377, c_75149])).
% 23.78/14.53  tff(c_75692, plain, (![A_1719, B_1720, C_1721, D_1722]: (v1_funct_1(k2_partfun1(A_1719, B_1720, C_1721, D_1722)) | ~m1_subset_1(C_1721, k1_zfmisc_1(k2_zfmisc_1(A_1719, B_1720))) | ~v1_funct_1(C_1721))), inference(cnfTransformation, [status(thm)], [f_113])).
% 23.78/14.53  tff(c_75695, plain, (![A_1719, B_1720, D_1722]: (v1_funct_1(k2_partfun1(A_1719, B_1720, '#skF_4', D_1722)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_75394, c_75692])).
% 23.78/14.53  tff(c_75698, plain, (![A_1719, B_1720, D_1722]: (v1_funct_1(k2_partfun1(A_1719, B_1720, '#skF_4', D_1722)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_75695])).
% 23.78/14.53  tff(c_75194, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_75186])).
% 23.78/14.53  tff(c_75203, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75150, c_75194])).
% 23.78/14.53  tff(c_75210, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75203, c_75156, c_75203, c_75203, c_75156, c_75156, c_75203, c_75203, c_75156, c_75156, c_62])).
% 23.78/14.53  tff(c_75211, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_75210])).
% 23.78/14.53  tff(c_75386, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75377, c_75377, c_75377, c_75211])).
% 23.78/14.53  tff(c_75701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75698, c_75386])).
% 23.78/14.53  tff(c_75702, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_75210])).
% 23.78/14.53  tff(c_75789, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_75702])).
% 23.78/14.53  tff(c_76138, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_75868, c_75868, c_75868, c_75868, c_75868, c_75789])).
% 23.78/14.53  tff(c_76335, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76333, c_76138])).
% 23.78/14.53  tff(c_76339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75883, c_76335])).
% 23.78/14.53  tff(c_76341, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_75702])).
% 23.78/14.53  tff(c_76622, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_76413, c_76413, c_76413, c_76413, c_76341])).
% 23.78/14.53  tff(c_34, plain, (![C_26, A_23, B_24]: (v1_xboole_0(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.78/14.53  tff(c_76630, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76622, c_34])).
% 23.78/14.53  tff(c_76644, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76407, c_76630])).
% 23.78/14.53  tff(c_76430, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_75163])).
% 23.78/14.53  tff(c_76658, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_76644, c_76430])).
% 23.78/14.53  tff(c_76340, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_75702])).
% 23.78/14.53  tff(c_76415, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76413, c_76413, c_76413, c_76413, c_76413, c_76340])).
% 23.78/14.53  tff(c_76685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76680, c_76658, c_76415])).
% 23.78/14.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.78/14.53  
% 23.78/14.53  Inference rules
% 23.78/14.53  ----------------------
% 23.78/14.53  #Ref     : 0
% 23.78/14.53  #Sup     : 15678
% 23.78/14.53  #Fact    : 0
% 23.78/14.53  #Define  : 0
% 23.78/14.53  #Split   : 37
% 23.78/14.53  #Chain   : 0
% 23.78/14.53  #Close   : 0
% 23.78/14.53  
% 23.78/14.53  Ordering : KBO
% 23.78/14.53  
% 23.78/14.53  Simplification rules
% 23.78/14.53  ----------------------
% 23.78/14.53  #Subsume      : 4548
% 23.78/14.53  #Demod        : 37639
% 23.78/14.53  #Tautology    : 5719
% 23.78/14.53  #SimpNegUnit  : 319
% 23.78/14.53  #BackRed      : 182
% 23.78/14.53  
% 23.78/14.53  #Partial instantiations: 0
% 23.78/14.53  #Strategies tried      : 1
% 23.78/14.53  
% 23.78/14.53  Timing (in seconds)
% 23.78/14.53  ----------------------
% 23.78/14.53  Preprocessing        : 0.35
% 23.78/14.53  Parsing              : 0.18
% 23.78/14.53  CNF conversion       : 0.02
% 23.78/14.53  Main loop            : 13.33
% 23.78/14.53  Inferencing          : 2.25
% 23.78/14.53  Reduction            : 6.41
% 23.78/14.53  Demodulation         : 5.45
% 23.78/14.53  BG Simplification    : 0.22
% 23.78/14.53  Subsumption          : 3.91
% 23.78/14.53  Abstraction          : 0.44
% 23.78/14.53  MUC search           : 0.00
% 23.78/14.53  Cooper               : 0.00
% 23.78/14.53  Total                : 13.74
% 23.78/14.53  Index Insertion      : 0.00
% 23.78/14.53  Index Deletion       : 0.00
% 23.78/14.53  Index Matching       : 0.00
% 23.78/14.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
