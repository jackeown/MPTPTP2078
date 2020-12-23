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
% DateTime   : Thu Dec  3 10:11:16 EST 2020

% Result     : Theorem 28.74s
% Output     : CNFRefutation 29.13s
% Verified   : 
% Statistics : Number of formulae       :  307 (1864 expanded)
%              Number of leaves         :   37 ( 610 expanded)
%              Depth                    :   24
%              Number of atoms          :  642 (5541 expanded)
%              Number of equality atoms :  127 (1415 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_138,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_38,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_77179,plain,(
    ! [B_1851,A_1852] :
      ( v1_relat_1(B_1851)
      | ~ m1_subset_1(B_1851,k1_zfmisc_1(A_1852))
      | ~ v1_relat_1(A_1852) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77185,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_77179])).

tff(c_77192,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_77185])).

tff(c_77322,plain,(
    ! [C_1868,B_1869,A_1870] :
      ( v5_relat_1(C_1868,B_1869)
      | ~ m1_subset_1(C_1868,k1_zfmisc_1(k2_zfmisc_1(A_1870,B_1869))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_77341,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_77322])).

tff(c_77408,plain,(
    ! [B_1883,A_1884] :
      ( r1_tarski(k2_relat_1(B_1883),A_1884)
      | ~ v5_relat_1(B_1883,A_1884)
      | ~ v1_relat_1(B_1883) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_77216,plain,(
    ! [A_1855,C_1856,B_1857] :
      ( r1_tarski(A_1855,C_1856)
      | ~ r1_tarski(B_1857,C_1856)
      | ~ r1_tarski(A_1855,B_1857) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77228,plain,(
    ! [A_1855] :
      ( r1_tarski(A_1855,'#skF_3')
      | ~ r1_tarski(A_1855,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_77216])).

tff(c_77441,plain,(
    ! [B_1883] :
      ( r1_tarski(k2_relat_1(B_1883),'#skF_3')
      | ~ v5_relat_1(B_1883,'#skF_2')
      | ~ v1_relat_1(B_1883) ) ),
    inference(resolution,[status(thm)],[c_77408,c_77228])).

tff(c_77568,plain,(
    ! [C_1891,A_1892,B_1893] :
      ( v4_relat_1(C_1891,A_1892)
      | ~ m1_subset_1(C_1891,k1_zfmisc_1(k2_zfmisc_1(A_1892,B_1893))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_77587,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_77568])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78709,plain,(
    ! [C_2002,A_2003,B_2004] :
      ( m1_subset_1(C_2002,k1_zfmisc_1(k2_zfmisc_1(A_2003,B_2004)))
      | ~ r1_tarski(k2_relat_1(C_2002),B_2004)
      | ~ r1_tarski(k1_relat_1(C_2002),A_2003)
      | ~ v1_relat_1(C_2002) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_168,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(A_54)
      | ~ v1_relat_1(B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_152])).

tff(c_187,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_168])).

tff(c_188,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60])).

tff(c_151,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_870,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_889,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_870])).

tff(c_1679,plain,(
    ! [B_201,A_202,C_203] :
      ( k1_xboole_0 = B_201
      | k1_relset_1(A_202,B_201,C_203) = A_202
      | ~ v1_funct_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1689,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1679])).

tff(c_1704,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_889,c_1689])).

tff(c_1705,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1704])).

tff(c_158,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_152])).

tff(c_165,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_158])).

tff(c_207,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_226,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_207])).

tff(c_469,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k2_relat_1(B_94),A_95)
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_299,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_314,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,'#skF_3')
      | ~ r1_tarski(A_77,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_299])).

tff(c_503,plain,(
    ! [B_94] :
      ( r1_tarski(k2_relat_1(B_94),'#skF_3')
      | ~ v5_relat_1(B_94,'#skF_2')
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_469,c_314])).

tff(c_1413,plain,(
    ! [C_181,A_182,B_183] :
      ( m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ r1_tarski(k2_relat_1(C_181),B_183)
      | ~ r1_tarski(k1_relat_1(C_181),A_182)
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3497,plain,(
    ! [C_301,A_302,B_303] :
      ( r1_tarski(C_301,k2_zfmisc_1(A_302,B_303))
      | ~ r1_tarski(k2_relat_1(C_301),B_303)
      | ~ r1_tarski(k1_relat_1(C_301),A_302)
      | ~ v1_relat_1(C_301) ) ),
    inference(resolution,[status(thm)],[c_1413,c_22])).

tff(c_3547,plain,(
    ! [B_305,A_306] :
      ( r1_tarski(B_305,k2_zfmisc_1(A_306,'#skF_3'))
      | ~ r1_tarski(k1_relat_1(B_305),A_306)
      | ~ v5_relat_1(B_305,'#skF_2')
      | ~ v1_relat_1(B_305) ) ),
    inference(resolution,[status(thm)],[c_503,c_3497])).

tff(c_3553,plain,(
    ! [A_306] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_306,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_306)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_3547])).

tff(c_3584,plain,(
    ! [A_307] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_307,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_226,c_3553])).

tff(c_888,plain,(
    ! [A_130,B_131,A_11] :
      ( k1_relset_1(A_130,B_131,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_130,B_131)) ) ),
    inference(resolution,[status(thm)],[c_24,c_870])).

tff(c_3587,plain,(
    ! [A_307] :
      ( k1_relset_1(A_307,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_307) ) ),
    inference(resolution,[status(thm)],[c_3584,c_888])).

tff(c_3620,plain,(
    ! [A_308] :
      ( k1_relset_1(A_308,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1705,c_3587])).

tff(c_3630,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_3620])).

tff(c_3771,plain,(
    ! [B_318] :
      ( r1_tarski(B_318,k2_zfmisc_1(k1_relat_1(B_318),'#skF_3'))
      | ~ v5_relat_1(B_318,'#skF_2')
      | ~ v1_relat_1(B_318) ) ),
    inference(resolution,[status(thm)],[c_6,c_3547])).

tff(c_3828,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3'))
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_3771])).

tff(c_3856,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_226,c_3828])).

tff(c_1861,plain,(
    ! [B_206,C_207,A_208] :
      ( k1_xboole_0 = B_206
      | v1_funct_2(C_207,A_208,B_206)
      | k1_relset_1(A_208,B_206,C_207) != A_208
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4092,plain,(
    ! [B_323,A_324,A_325] :
      ( k1_xboole_0 = B_323
      | v1_funct_2(A_324,A_325,B_323)
      | k1_relset_1(A_325,B_323,A_324) != A_325
      | ~ r1_tarski(A_324,k2_zfmisc_1(A_325,B_323)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1861])).

tff(c_4101,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_3856,c_4092])).

tff(c_4156,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_4101])).

tff(c_4157,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_4156])).

tff(c_83,plain,(
    ! [A_42] : k2_zfmisc_1(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_4247,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4157,c_87])).

tff(c_4252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_4247])).

tff(c_4253,plain,(
    v1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_4254,plain,(
    v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_4870,plain,(
    ! [A_396,B_397,C_398] :
      ( k1_relset_1(A_396,B_397,C_398) = k1_relat_1(C_398)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_396,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4889,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4870])).

tff(c_5835,plain,(
    ! [B_482,A_483,C_484] :
      ( k1_xboole_0 = B_482
      | k1_relset_1(A_483,B_482,C_484) = A_483
      | ~ v1_funct_2(C_484,A_483,B_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_483,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5845,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5835])).

tff(c_5860,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4889,c_5845])).

tff(c_5861,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5860])).

tff(c_4272,plain,(
    ! [C_328,B_329,A_330] :
      ( v5_relat_1(C_328,B_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4291,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4272])).

tff(c_4622,plain,(
    ! [B_377,A_378] :
      ( r1_tarski(k2_relat_1(B_377),A_378)
      | ~ v5_relat_1(B_377,A_378)
      | ~ v1_relat_1(B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4459,plain,(
    ! [A_360,C_361,B_362] :
      ( r1_tarski(A_360,C_361)
      | ~ r1_tarski(B_362,C_361)
      | ~ r1_tarski(A_360,B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4474,plain,(
    ! [A_360] :
      ( r1_tarski(A_360,'#skF_3')
      | ~ r1_tarski(A_360,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_4459])).

tff(c_4662,plain,(
    ! [B_377] :
      ( r1_tarski(k2_relat_1(B_377),'#skF_3')
      | ~ v5_relat_1(B_377,'#skF_2')
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_4622,c_4474])).

tff(c_5433,plain,(
    ! [C_453,A_454,B_455] :
      ( m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ r1_tarski(k2_relat_1(C_453),B_455)
      | ~ r1_tarski(k1_relat_1(C_453),A_454)
      | ~ v1_relat_1(C_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7203,plain,(
    ! [C_556,A_557,B_558] :
      ( r1_tarski(C_556,k2_zfmisc_1(A_557,B_558))
      | ~ r1_tarski(k2_relat_1(C_556),B_558)
      | ~ r1_tarski(k1_relat_1(C_556),A_557)
      | ~ v1_relat_1(C_556) ) ),
    inference(resolution,[status(thm)],[c_5433,c_22])).

tff(c_7346,plain,(
    ! [B_565,A_566] :
      ( r1_tarski(B_565,k2_zfmisc_1(A_566,'#skF_3'))
      | ~ r1_tarski(k1_relat_1(B_565),A_566)
      | ~ v5_relat_1(B_565,'#skF_2')
      | ~ v1_relat_1(B_565) ) ),
    inference(resolution,[status(thm)],[c_4662,c_7203])).

tff(c_7353,plain,(
    ! [A_566] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_566,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_566)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5861,c_7346])).

tff(c_7384,plain,(
    ! [A_567] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_567,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_4291,c_7353])).

tff(c_4888,plain,(
    ! [A_396,B_397,A_11] :
      ( k1_relset_1(A_396,B_397,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_396,B_397)) ) ),
    inference(resolution,[status(thm)],[c_24,c_4870])).

tff(c_7387,plain,(
    ! [A_567] :
      ( k1_relset_1(A_567,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_567) ) ),
    inference(resolution,[status(thm)],[c_7384,c_4888])).

tff(c_7420,plain,(
    ! [A_568] :
      ( k1_relset_1(A_568,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5861,c_7387])).

tff(c_7435,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_7420])).

tff(c_7440,plain,(
    ! [B_569] :
      ( r1_tarski(B_569,k2_zfmisc_1(k1_relat_1(B_569),'#skF_3'))
      | ~ v5_relat_1(B_569,'#skF_2')
      | ~ v1_relat_1(B_569) ) ),
    inference(resolution,[status(thm)],[c_6,c_7346])).

tff(c_7488,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3'))
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5861,c_7440])).

tff(c_7513,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_4291,c_7488])).

tff(c_5565,plain,(
    ! [B_460,C_461,A_462] :
      ( k1_xboole_0 = B_460
      | v1_funct_2(C_461,A_462,B_460)
      | k1_relset_1(A_462,B_460,C_461) != A_462
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_462,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7547,plain,(
    ! [B_570,A_571,A_572] :
      ( k1_xboole_0 = B_570
      | v1_funct_2(A_571,A_572,B_570)
      | k1_relset_1(A_572,B_570,A_571) != A_572
      | ~ r1_tarski(A_571,k2_zfmisc_1(A_572,B_570)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5565])).

tff(c_7550,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_7513,c_7547])).

tff(c_7598,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_7550])).

tff(c_7599,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_7598])).

tff(c_7691,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7599,c_10])).

tff(c_125,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_4524,plain,(
    ! [A_368] :
      ( r1_tarski(A_368,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_368,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_4459])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5380,plain,(
    ! [A_448,A_449] :
      ( r1_tarski(A_448,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_448,A_449)
      | ~ r1_tarski(A_449,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4524,c_8])).

tff(c_5415,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_5380])).

tff(c_5426,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5415])).

tff(c_7773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7691,c_5426])).

tff(c_7775,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5415])).

tff(c_4542,plain,(
    ! [A_3,A_368] :
      ( r1_tarski(A_3,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_3,A_368)
      | ~ r1_tarski(A_368,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4524,c_8])).

tff(c_7777,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_7775,c_4542])).

tff(c_7790,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7777])).

tff(c_4290,plain,(
    ! [A_11,B_329,A_330] :
      ( v5_relat_1(A_11,B_329)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_330,B_329)) ) ),
    inference(resolution,[status(thm)],[c_24,c_4272])).

tff(c_7894,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_7790,c_4290])).

tff(c_4801,plain,(
    ! [B_391] :
      ( r1_tarski(k2_relat_1(B_391),'#skF_3')
      | ~ v5_relat_1(B_391,'#skF_2')
      | ~ v1_relat_1(B_391) ) ),
    inference(resolution,[status(thm)],[c_4622,c_4474])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( v5_relat_1(B_22,A_21)
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4816,plain,(
    ! [B_391] :
      ( v5_relat_1(B_391,'#skF_3')
      | ~ v5_relat_1(B_391,'#skF_2')
      | ~ v1_relat_1(B_391) ) ),
    inference(resolution,[status(thm)],[c_4801,c_34])).

tff(c_7909,plain,
    ( v5_relat_1('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7894,c_4816])).

tff(c_7915,plain,(
    v5_relat_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_7909])).

tff(c_4823,plain,(
    ! [B_392] :
      ( v5_relat_1(B_392,'#skF_3')
      | ~ v5_relat_1(B_392,'#skF_2')
      | ~ v1_relat_1(B_392) ) ),
    inference(resolution,[status(thm)],[c_4801,c_34])).

tff(c_4841,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4291,c_4823])).

tff(c_4852,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_4841])).

tff(c_7921,plain,(
    ! [B_577,A_578,C_579] :
      ( k1_xboole_0 = B_577
      | k1_relset_1(A_578,B_577,C_579) = A_578
      | ~ v1_funct_2(C_579,A_578,B_577)
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_578,B_577))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7931,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_7921])).

tff(c_7946,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4889,c_7931])).

tff(c_7947,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_7946])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7838,plain,(
    ! [C_574,A_575,B_576] :
      ( m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(A_575,B_576)))
      | ~ r1_tarski(k2_relat_1(C_574),B_576)
      | ~ r1_tarski(k1_relat_1(C_574),A_575)
      | ~ v1_relat_1(C_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9672,plain,(
    ! [C_659,A_660,B_661] :
      ( r1_tarski(C_659,k2_zfmisc_1(A_660,B_661))
      | ~ r1_tarski(k2_relat_1(C_659),B_661)
      | ~ r1_tarski(k1_relat_1(C_659),A_660)
      | ~ v1_relat_1(C_659) ) ),
    inference(resolution,[status(thm)],[c_7838,c_22])).

tff(c_14393,plain,(
    ! [B_852,A_853,A_854] :
      ( r1_tarski(B_852,k2_zfmisc_1(A_853,A_854))
      | ~ r1_tarski(k1_relat_1(B_852),A_853)
      | ~ v5_relat_1(B_852,A_854)
      | ~ v1_relat_1(B_852) ) ),
    inference(resolution,[status(thm)],[c_36,c_9672])).

tff(c_14446,plain,(
    ! [B_855,A_856] :
      ( r1_tarski(B_855,k2_zfmisc_1(k1_relat_1(B_855),A_856))
      | ~ v5_relat_1(B_855,A_856)
      | ~ v1_relat_1(B_855) ) ),
    inference(resolution,[status(thm)],[c_6,c_14393])).

tff(c_14532,plain,(
    ! [A_856] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',A_856))
      | ~ v5_relat_1('#skF_4',A_856)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7947,c_14446])).

tff(c_14578,plain,(
    ! [A_857] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',A_857))
      | ~ v5_relat_1('#skF_4',A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_14532])).

tff(c_14591,plain,(
    ! [A_857] :
      ( k1_relset_1('#skF_1',A_857,'#skF_4') = k1_relat_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_857) ) ),
    inference(resolution,[status(thm)],[c_14578,c_4888])).

tff(c_14630,plain,(
    ! [A_858] :
      ( k1_relset_1('#skF_1',A_858,'#skF_4') = '#skF_1'
      | ~ v5_relat_1('#skF_4',A_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7947,c_14591])).

tff(c_14749,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4852,c_14630])).

tff(c_46,plain,(
    ! [C_33,A_31,B_32] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r1_tarski(k2_relat_1(C_33),B_32)
      | ~ r1_tarski(k1_relat_1(C_33),A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8057,plain,(
    ! [B_581,C_582,A_583] :
      ( k1_xboole_0 = B_581
      | v1_funct_2(C_582,A_583,B_581)
      | k1_relset_1(A_583,B_581,C_582) != A_583
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(A_583,B_581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11554,plain,(
    ! [B_747,C_748,A_749] :
      ( k1_xboole_0 = B_747
      | v1_funct_2(C_748,A_749,B_747)
      | k1_relset_1(A_749,B_747,C_748) != A_749
      | ~ r1_tarski(k2_relat_1(C_748),B_747)
      | ~ r1_tarski(k1_relat_1(C_748),A_749)
      | ~ v1_relat_1(C_748) ) ),
    inference(resolution,[status(thm)],[c_46,c_8057])).

tff(c_20630,plain,(
    ! [A_991,B_992,A_993] :
      ( k1_xboole_0 = A_991
      | v1_funct_2(B_992,A_993,A_991)
      | k1_relset_1(A_993,A_991,B_992) != A_993
      | ~ r1_tarski(k1_relat_1(B_992),A_993)
      | ~ v5_relat_1(B_992,A_991)
      | ~ v1_relat_1(B_992) ) ),
    inference(resolution,[status(thm)],[c_36,c_11554])).

tff(c_20674,plain,(
    ! [A_991,A_993] :
      ( k1_xboole_0 = A_991
      | v1_funct_2('#skF_4',A_993,A_991)
      | k1_relset_1(A_993,A_991,'#skF_4') != A_993
      | ~ r1_tarski('#skF_1',A_993)
      | ~ v5_relat_1('#skF_4',A_991)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7947,c_20630])).

tff(c_76269,plain,(
    ! [A_1846,A_1847] :
      ( k1_xboole_0 = A_1846
      | v1_funct_2('#skF_4',A_1847,A_1846)
      | k1_relset_1(A_1847,A_1846,'#skF_4') != A_1847
      | ~ r1_tarski('#skF_1',A_1847)
      | ~ v5_relat_1('#skF_4',A_1846) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_20674])).

tff(c_76304,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_76269,c_151])).

tff(c_76333,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4852,c_6,c_14749,c_76304])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4370,plain,(
    ! [C_346,A_347,B_348] :
      ( v4_relat_1(C_346,A_347)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4415,plain,(
    ! [C_353,A_354] :
      ( v4_relat_1(C_353,A_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4370])).

tff(c_4422,plain,(
    ! [A_11,A_354] :
      ( v4_relat_1(A_11,A_354)
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_4415])).

tff(c_4491,plain,(
    ! [A_365,A_366] :
      ( r1_tarski(A_365,A_366)
      | ~ r1_tarski(A_365,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_4459])).

tff(c_4501,plain,(
    ! [B_20,A_366] :
      ( r1_tarski(k1_relat_1(B_20),A_366)
      | ~ v4_relat_1(B_20,k1_xboole_0)
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_4491])).

tff(c_44,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10504,plain,(
    ! [A_701,B_702,C_703] :
      ( k1_relset_1(A_701,B_702,C_703) = k1_relat_1(C_703)
      | ~ r1_tarski(k2_relat_1(C_703),B_702)
      | ~ r1_tarski(k1_relat_1(C_703),A_701)
      | ~ v1_relat_1(C_703) ) ),
    inference(resolution,[status(thm)],[c_7838,c_44])).

tff(c_17073,plain,(
    ! [A_917,A_918,B_919] :
      ( k1_relset_1(A_917,A_918,B_919) = k1_relat_1(B_919)
      | ~ r1_tarski(k1_relat_1(B_919),A_917)
      | ~ v5_relat_1(B_919,A_918)
      | ~ v1_relat_1(B_919) ) ),
    inference(resolution,[status(thm)],[c_36,c_10504])).

tff(c_39035,plain,(
    ! [A_1372,A_1373,B_1374] :
      ( k1_relset_1(A_1372,A_1373,B_1374) = k1_relat_1(B_1374)
      | ~ v5_relat_1(B_1374,A_1373)
      | ~ v4_relat_1(B_1374,k1_xboole_0)
      | ~ v1_relat_1(B_1374) ) ),
    inference(resolution,[status(thm)],[c_4501,c_17073])).

tff(c_39217,plain,(
    ! [A_1372] :
      ( k1_relset_1(A_1372,'#skF_2','#skF_3') = k1_relat_1('#skF_3')
      | ~ v4_relat_1('#skF_3',k1_xboole_0)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7894,c_39035])).

tff(c_39466,plain,(
    ! [A_1372] :
      ( k1_relset_1(A_1372,'#skF_2','#skF_3') = k1_relat_1('#skF_3')
      | ~ v4_relat_1('#skF_3',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_39217])).

tff(c_59015,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_39466])).

tff(c_59029,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4422,c_59015])).

tff(c_4596,plain,(
    ! [B_374,A_375] :
      ( v4_relat_1(B_374,A_375)
      | ~ r1_tarski(k1_relat_1(B_374),A_375)
      | ~ v1_relat_1(B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4615,plain,(
    ! [B_374] :
      ( v4_relat_1(B_374,k1_relat_1(B_374))
      | ~ v1_relat_1(B_374) ) ),
    inference(resolution,[status(thm)],[c_6,c_4596])).

tff(c_4388,plain,(
    ! [A_11,A_347,B_348] :
      ( v4_relat_1(A_11,A_347)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_347,B_348)) ) ),
    inference(resolution,[status(thm)],[c_24,c_4370])).

tff(c_7893,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_7790,c_4388])).

tff(c_8529,plain,(
    ! [A_603,A_604,B_605] :
      ( r1_tarski(A_603,A_604)
      | ~ r1_tarski(A_603,k1_relat_1(B_605))
      | ~ v4_relat_1(B_605,A_604)
      | ~ v1_relat_1(B_605) ) ),
    inference(resolution,[status(thm)],[c_32,c_4459])).

tff(c_16332,plain,(
    ! [B_900,A_901,B_902] :
      ( r1_tarski(k1_relat_1(B_900),A_901)
      | ~ v4_relat_1(B_902,A_901)
      | ~ v1_relat_1(B_902)
      | ~ v4_relat_1(B_900,k1_relat_1(B_902))
      | ~ v1_relat_1(B_900) ) ),
    inference(resolution,[status(thm)],[c_32,c_8529])).

tff(c_16384,plain,(
    ! [B_900] :
      ( r1_tarski(k1_relat_1(B_900),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v4_relat_1(B_900,k1_relat_1('#skF_3'))
      | ~ v1_relat_1(B_900) ) ),
    inference(resolution,[status(thm)],[c_7893,c_16332])).

tff(c_70804,plain,(
    ! [B_1793] :
      ( r1_tarski(k1_relat_1(B_1793),'#skF_1')
      | ~ v4_relat_1(B_1793,k1_relat_1('#skF_3'))
      | ~ v1_relat_1(B_1793) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_16384])).

tff(c_70900,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4615,c_70804])).

tff(c_70968,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_70900])).

tff(c_9705,plain,(
    ! [B_22,A_660,A_21] :
      ( r1_tarski(B_22,k2_zfmisc_1(A_660,A_21))
      | ~ r1_tarski(k1_relat_1(B_22),A_660)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_36,c_9672])).

tff(c_71000,plain,(
    ! [A_21] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',A_21))
      | ~ v5_relat_1('#skF_3',A_21)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70968,c_9705])).

tff(c_72741,plain,(
    ! [A_1808] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',A_1808))
      | ~ v5_relat_1('#skF_3',A_1808) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_71000])).

tff(c_72773,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_72741])).

tff(c_72791,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_59029,c_72773])).

tff(c_76337,plain,(
    ~ v5_relat_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76333,c_72791])).

tff(c_76468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7915,c_76337])).

tff(c_76470,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_39466])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9312,plain,(
    ! [C_641,B_642] :
      ( m1_subset_1(C_641,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_641),B_642)
      | ~ r1_tarski(k1_relat_1(C_641),k1_xboole_0)
      | ~ v1_relat_1(C_641) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_7838])).

tff(c_9452,plain,(
    ! [C_647] :
      ( m1_subset_1(C_647,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_647),k1_xboole_0)
      | ~ v1_relat_1(C_647) ) ),
    inference(resolution,[status(thm)],[c_6,c_9312])).

tff(c_9486,plain,(
    ! [B_650] :
      ( m1_subset_1(B_650,k1_zfmisc_1(k1_xboole_0))
      | ~ v4_relat_1(B_650,k1_xboole_0)
      | ~ v1_relat_1(B_650) ) ),
    inference(resolution,[status(thm)],[c_4501,c_9452])).

tff(c_9514,plain,(
    ! [B_650] :
      ( r1_tarski(B_650,k1_xboole_0)
      | ~ v4_relat_1(B_650,k1_xboole_0)
      | ~ v1_relat_1(B_650) ) ),
    inference(resolution,[status(thm)],[c_9486,c_22])).

tff(c_76484,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76470,c_9514])).

tff(c_76509,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_76484])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76902,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_76509,c_2])).

tff(c_76930,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_76902])).

tff(c_4320,plain,(
    ! [C_336,B_337] :
      ( v5_relat_1(C_336,B_337)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4272])).

tff(c_4327,plain,(
    ! [A_11,B_337] :
      ( v5_relat_1(A_11,B_337)
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_4320])).

tff(c_4472,plain,(
    ! [A_360,A_6] :
      ( r1_tarski(A_360,A_6)
      | ~ r1_tarski(A_360,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_4459])).

tff(c_4663,plain,(
    ! [B_377,A_6] :
      ( r1_tarski(k2_relat_1(B_377),A_6)
      | ~ v5_relat_1(B_377,k1_xboole_0)
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_4622,c_4472])).

tff(c_8211,plain,(
    ! [A_587,B_588,A_589] :
      ( k1_relset_1(A_587,B_588,A_589) = k1_relat_1(A_589)
      | ~ r1_tarski(A_589,k2_zfmisc_1(A_587,B_588)) ) ),
    inference(resolution,[status(thm)],[c_24,c_4870])).

tff(c_35302,plain,(
    ! [A_1325,B_1326,B_1327] :
      ( k1_relset_1(A_1325,B_1326,k2_relat_1(B_1327)) = k1_relat_1(k2_relat_1(B_1327))
      | ~ v5_relat_1(B_1327,k1_xboole_0)
      | ~ v1_relat_1(B_1327) ) ),
    inference(resolution,[status(thm)],[c_4663,c_8211])).

tff(c_4408,plain,(
    ! [B_350,A_351] :
      ( v5_relat_1(B_350,A_351)
      | ~ r1_tarski(k2_relat_1(B_350),A_351)
      | ~ v1_relat_1(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4413,plain,(
    ! [B_350] :
      ( v5_relat_1(B_350,k2_relat_1(B_350))
      | ~ v1_relat_1(B_350) ) ),
    inference(resolution,[status(thm)],[c_6,c_4408])).

tff(c_7774,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5415])).

tff(c_7817,plain,(
    v5_relat_1('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7774,c_4290])).

tff(c_8748,plain,(
    ! [A_614,A_615,B_616] :
      ( r1_tarski(A_614,A_615)
      | ~ r1_tarski(A_614,k2_relat_1(B_616))
      | ~ v5_relat_1(B_616,A_615)
      | ~ v1_relat_1(B_616) ) ),
    inference(resolution,[status(thm)],[c_4622,c_8])).

tff(c_16550,plain,(
    ! [B_905,A_906,B_907] :
      ( r1_tarski(k2_relat_1(B_905),A_906)
      | ~ v5_relat_1(B_907,A_906)
      | ~ v1_relat_1(B_907)
      | ~ v5_relat_1(B_905,k2_relat_1(B_907))
      | ~ v1_relat_1(B_905) ) ),
    inference(resolution,[status(thm)],[c_36,c_8748])).

tff(c_16624,plain,(
    ! [B_905] :
      ( r1_tarski(k2_relat_1(B_905),'#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v5_relat_1(B_905,k2_relat_1('#skF_2'))
      | ~ v1_relat_1(B_905) ) ),
    inference(resolution,[status(thm)],[c_7817,c_16550])).

tff(c_33168,plain,(
    ! [B_1297] :
      ( r1_tarski(k2_relat_1(B_1297),'#skF_2')
      | ~ v5_relat_1(B_1297,k2_relat_1('#skF_2'))
      | ~ v1_relat_1(B_1297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_16624])).

tff(c_33220,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4413,c_33168])).

tff(c_33255,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_33220])).

tff(c_8563,plain,(
    ! [A_606] :
      ( r1_tarski(A_606,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_606,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7790,c_8])).

tff(c_8600,plain,(
    ! [A_3,A_606] :
      ( r1_tarski(A_3,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_3,A_606)
      | ~ r1_tarski(A_606,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8563,c_8])).

tff(c_33519,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_33255,c_8600])).

tff(c_33556,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_33519])).

tff(c_8079,plain,(
    ! [B_581,A_11,A_583] :
      ( k1_xboole_0 = B_581
      | v1_funct_2(A_11,A_583,B_581)
      | k1_relset_1(A_583,B_581,A_11) != A_583
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_583,B_581)) ) ),
    inference(resolution,[status(thm)],[c_24,c_8057])).

tff(c_33708,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_relat_1('#skF_2'),'#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2',k2_relat_1('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_33556,c_8079])).

tff(c_33747,plain,
    ( v1_funct_2(k2_relat_1('#skF_2'),'#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2',k2_relat_1('#skF_2')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_33708])).

tff(c_33874,plain,(
    k1_relset_1('#skF_1','#skF_2',k2_relat_1('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_33747])).

tff(c_35308,plain,
    ( k1_relat_1(k2_relat_1('#skF_2')) != '#skF_1'
    | ~ v5_relat_1('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35302,c_33874])).

tff(c_35363,plain,
    ( k1_relat_1(k2_relat_1('#skF_2')) != '#skF_1'
    | ~ v5_relat_1('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_35308])).

tff(c_35381,plain,(
    ~ v5_relat_1('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_35363])).

tff(c_35391,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4327,c_35381])).

tff(c_76942,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76930,c_35391])).

tff(c_77054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_76942])).

tff(c_77056,plain,(
    v5_relat_1('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_35363])).

tff(c_9473,plain,(
    ! [C_648,A_649] :
      ( m1_subset_1(C_648,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_648),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_648),A_649)
      | ~ v1_relat_1(C_648) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7838])).

tff(c_13596,plain,(
    ! [B_818,A_819] :
      ( m1_subset_1(B_818,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(B_818),A_819)
      | ~ v5_relat_1(B_818,k1_xboole_0)
      | ~ v1_relat_1(B_818) ) ),
    inference(resolution,[status(thm)],[c_36,c_9473])).

tff(c_13751,plain,(
    ! [B_822] :
      ( m1_subset_1(B_822,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_relat_1(B_822,k1_xboole_0)
      | ~ v1_relat_1(B_822) ) ),
    inference(resolution,[status(thm)],[c_6,c_13596])).

tff(c_13779,plain,(
    ! [B_822] :
      ( r1_tarski(B_822,k1_xboole_0)
      | ~ v5_relat_1(B_822,k1_xboole_0)
      | ~ v1_relat_1(B_822) ) ),
    inference(resolution,[status(thm)],[c_13751,c_22])).

tff(c_77067,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_77056,c_13779])).

tff(c_77091,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_77067])).

tff(c_77125,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_77091,c_2])).

tff(c_77153,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77125])).

tff(c_77155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_77153])).

tff(c_77156,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_78726,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78709,c_77156])).

tff(c_78745,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77192,c_78726])).

tff(c_78747,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78745])).

tff(c_78753,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_78747])).

tff(c_78760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77192,c_77587,c_78753])).

tff(c_78761,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_78745])).

tff(c_78798,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77441,c_78761])).

tff(c_78808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77192,c_77341,c_78798])).

tff(c_78809,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_78812,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78809,c_78809,c_16])).

tff(c_78810,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_78819,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78809,c_78810])).

tff(c_78858,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78812,c_78819,c_66])).

tff(c_78875,plain,(
    ! [A_2012,B_2013] :
      ( r1_tarski(A_2012,B_2013)
      | ~ m1_subset_1(A_2012,k1_zfmisc_1(B_2013)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78882,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_78858,c_78875])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78859,plain,(
    ! [A_7] :
      ( A_7 = '#skF_1'
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78809,c_78809,c_12])).

tff(c_78888,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78882,c_78859])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78813,plain,(
    ! [A_10] : m1_subset_1('#skF_1',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78809,c_20])).

tff(c_78901,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78888,c_78813])).

tff(c_78839,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_1',B_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78809,c_78809,c_18])).

tff(c_78899,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78888,c_78888,c_78839])).

tff(c_79059,plain,(
    ! [C_2041,A_2042,B_2043] :
      ( v4_relat_1(C_2041,A_2042)
      | ~ m1_subset_1(C_2041,k1_zfmisc_1(k2_zfmisc_1(A_2042,B_2043))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_79125,plain,(
    ! [A_2053,A_2054,B_2055] :
      ( v4_relat_1(A_2053,A_2054)
      | ~ r1_tarski(A_2053,k2_zfmisc_1(A_2054,B_2055)) ) ),
    inference(resolution,[status(thm)],[c_24,c_79059])).

tff(c_79152,plain,(
    ! [A_2054,B_2055] : v4_relat_1(k2_zfmisc_1(A_2054,B_2055),A_2054) ),
    inference(resolution,[status(thm)],[c_6,c_79125])).

tff(c_79090,plain,(
    ! [B_2047,A_2048] :
      ( r1_tarski(k1_relat_1(B_2047),A_2048)
      | ~ v4_relat_1(B_2047,A_2048)
      | ~ v1_relat_1(B_2047) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78896,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78888,c_78888,c_78859])).

tff(c_79173,plain,(
    ! [B_2061] :
      ( k1_relat_1(B_2061) = '#skF_4'
      | ~ v4_relat_1(B_2061,'#skF_4')
      | ~ v1_relat_1(B_2061) ) ),
    inference(resolution,[status(thm)],[c_79090,c_78896])).

tff(c_79177,plain,(
    ! [B_2055] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_2055)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_2055)) ) ),
    inference(resolution,[status(thm)],[c_79152,c_79173])).

tff(c_79188,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_78899,c_79177])).

tff(c_79390,plain,(
    ! [A_2087,B_2088,C_2089] :
      ( k1_relset_1(A_2087,B_2088,C_2089) = k1_relat_1(C_2089)
      | ~ m1_subset_1(C_2089,k1_zfmisc_1(k2_zfmisc_1(A_2087,B_2088))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_79400,plain,(
    ! [A_2087,B_2088] : k1_relset_1(A_2087,B_2088,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78901,c_79390])).

tff(c_79406,plain,(
    ! [A_2087,B_2088] : k1_relset_1(A_2087,B_2088,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79188,c_79400])).

tff(c_78905,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78888,c_78809])).

tff(c_52,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_79548,plain,(
    ! [C_2100,B_2101] :
      ( v1_funct_2(C_2100,'#skF_4',B_2101)
      | k1_relset_1('#skF_4',B_2101,C_2100) != '#skF_4'
      | ~ m1_subset_1(C_2100,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78905,c_78905,c_78905,c_78905,c_76])).

tff(c_79551,plain,(
    ! [B_2101] :
      ( v1_funct_2('#skF_4','#skF_4',B_2101)
      | k1_relset_1('#skF_4',B_2101,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_78901,c_79548])).

tff(c_79557,plain,(
    ! [B_2101] : v1_funct_2('#skF_4','#skF_4',B_2101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79406,c_79551])).

tff(c_78915,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78888,c_78888,c_72])).

tff(c_78916,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78915])).

tff(c_79562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79557,c_78916])).

tff(c_79563,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_78915])).

tff(c_79637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78901,c_78899,c_79563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.74/18.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.78/18.69  
% 28.78/18.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.78/18.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 28.78/18.69  
% 28.78/18.69  %Foreground sorts:
% 28.78/18.69  
% 28.78/18.69  
% 28.78/18.69  %Background operators:
% 28.78/18.69  
% 28.78/18.69  
% 28.78/18.69  %Foreground operators:
% 28.78/18.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.78/18.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.78/18.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.78/18.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.78/18.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.78/18.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 28.78/18.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 28.78/18.69  tff('#skF_2', type, '#skF_2': $i).
% 28.78/18.69  tff('#skF_3', type, '#skF_3': $i).
% 28.78/18.69  tff('#skF_1', type, '#skF_1': $i).
% 28.78/18.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 28.78/18.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 28.78/18.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.78/18.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.78/18.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.78/18.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 28.78/18.69  tff('#skF_4', type, '#skF_4': $i).
% 28.78/18.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.78/18.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 28.78/18.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 28.78/18.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.78/18.69  
% 29.13/18.73  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 29.13/18.73  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 29.13/18.73  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 29.13/18.73  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 29.13/18.73  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 29.13/18.73  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 29.13/18.73  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 29.13/18.73  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 29.13/18.73  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 29.13/18.73  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 29.13/18.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.13/18.73  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 29.13/18.73  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 29.13/18.73  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 29.13/18.73  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 29.13/18.73  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 29.13/18.73  tff(c_38, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 29.13/18.73  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_77179, plain, (![B_1851, A_1852]: (v1_relat_1(B_1851) | ~m1_subset_1(B_1851, k1_zfmisc_1(A_1852)) | ~v1_relat_1(A_1852))), inference(cnfTransformation, [status(thm)], [f_68])).
% 29.13/18.73  tff(c_77185, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_77179])).
% 29.13/18.73  tff(c_77192, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_77185])).
% 29.13/18.73  tff(c_77322, plain, (![C_1868, B_1869, A_1870]: (v5_relat_1(C_1868, B_1869) | ~m1_subset_1(C_1868, k1_zfmisc_1(k2_zfmisc_1(A_1870, B_1869))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_77341, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_77322])).
% 29.13/18.73  tff(c_77408, plain, (![B_1883, A_1884]: (r1_tarski(k2_relat_1(B_1883), A_1884) | ~v5_relat_1(B_1883, A_1884) | ~v1_relat_1(B_1883))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_64, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_77216, plain, (![A_1855, C_1856, B_1857]: (r1_tarski(A_1855, C_1856) | ~r1_tarski(B_1857, C_1856) | ~r1_tarski(A_1855, B_1857))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.13/18.73  tff(c_77228, plain, (![A_1855]: (r1_tarski(A_1855, '#skF_3') | ~r1_tarski(A_1855, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_77216])).
% 29.13/18.73  tff(c_77441, plain, (![B_1883]: (r1_tarski(k2_relat_1(B_1883), '#skF_3') | ~v5_relat_1(B_1883, '#skF_2') | ~v1_relat_1(B_1883))), inference(resolution, [status(thm)], [c_77408, c_77228])).
% 29.13/18.73  tff(c_77568, plain, (![C_1891, A_1892, B_1893]: (v4_relat_1(C_1891, A_1892) | ~m1_subset_1(C_1891, k1_zfmisc_1(k2_zfmisc_1(A_1892, B_1893))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_77587, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_77568])).
% 29.13/18.73  tff(c_32, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 29.13/18.73  tff(c_78709, plain, (![C_2002, A_2003, B_2004]: (m1_subset_1(C_2002, k1_zfmisc_1(k2_zfmisc_1(A_2003, B_2004))) | ~r1_tarski(k2_relat_1(C_2002), B_2004) | ~r1_tarski(k1_relat_1(C_2002), A_2003) | ~v1_relat_1(C_2002))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.13/18.73  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_92, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 29.13/18.73  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.13/18.73  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.13/18.73  tff(c_152, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 29.13/18.73  tff(c_168, plain, (![A_54, B_55]: (v1_relat_1(A_54) | ~v1_relat_1(B_55) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_24, c_152])).
% 29.13/18.73  tff(c_187, plain, (v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_168])).
% 29.13/18.73  tff(c_188, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 29.13/18.73  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_72, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60])).
% 29.13/18.73  tff(c_151, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 29.13/18.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.13/18.73  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 29.13/18.73  tff(c_870, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.13/18.73  tff(c_889, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_870])).
% 29.13/18.73  tff(c_1679, plain, (![B_201, A_202, C_203]: (k1_xboole_0=B_201 | k1_relset_1(A_202, B_201, C_203)=A_202 | ~v1_funct_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_1689, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1679])).
% 29.13/18.73  tff(c_1704, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_889, c_1689])).
% 29.13/18.73  tff(c_1705, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_92, c_1704])).
% 29.13/18.73  tff(c_158, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_152])).
% 29.13/18.73  tff(c_165, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_158])).
% 29.13/18.73  tff(c_207, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_226, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_207])).
% 29.13/18.73  tff(c_469, plain, (![B_94, A_95]: (r1_tarski(k2_relat_1(B_94), A_95) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_299, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.13/18.73  tff(c_314, plain, (![A_77]: (r1_tarski(A_77, '#skF_3') | ~r1_tarski(A_77, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_299])).
% 29.13/18.73  tff(c_503, plain, (![B_94]: (r1_tarski(k2_relat_1(B_94), '#skF_3') | ~v5_relat_1(B_94, '#skF_2') | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_469, c_314])).
% 29.13/18.73  tff(c_1413, plain, (![C_181, A_182, B_183]: (m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~r1_tarski(k2_relat_1(C_181), B_183) | ~r1_tarski(k1_relat_1(C_181), A_182) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.13/18.73  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.13/18.73  tff(c_3497, plain, (![C_301, A_302, B_303]: (r1_tarski(C_301, k2_zfmisc_1(A_302, B_303)) | ~r1_tarski(k2_relat_1(C_301), B_303) | ~r1_tarski(k1_relat_1(C_301), A_302) | ~v1_relat_1(C_301))), inference(resolution, [status(thm)], [c_1413, c_22])).
% 29.13/18.73  tff(c_3547, plain, (![B_305, A_306]: (r1_tarski(B_305, k2_zfmisc_1(A_306, '#skF_3')) | ~r1_tarski(k1_relat_1(B_305), A_306) | ~v5_relat_1(B_305, '#skF_2') | ~v1_relat_1(B_305))), inference(resolution, [status(thm)], [c_503, c_3497])).
% 29.13/18.73  tff(c_3553, plain, (![A_306]: (r1_tarski('#skF_4', k2_zfmisc_1(A_306, '#skF_3')) | ~r1_tarski('#skF_1', A_306) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1705, c_3547])).
% 29.13/18.73  tff(c_3584, plain, (![A_307]: (r1_tarski('#skF_4', k2_zfmisc_1(A_307, '#skF_3')) | ~r1_tarski('#skF_1', A_307))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_226, c_3553])).
% 29.13/18.73  tff(c_888, plain, (![A_130, B_131, A_11]: (k1_relset_1(A_130, B_131, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_130, B_131)))), inference(resolution, [status(thm)], [c_24, c_870])).
% 29.13/18.73  tff(c_3587, plain, (![A_307]: (k1_relset_1(A_307, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_307))), inference(resolution, [status(thm)], [c_3584, c_888])).
% 29.13/18.73  tff(c_3620, plain, (![A_308]: (k1_relset_1(A_308, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_308))), inference(demodulation, [status(thm), theory('equality')], [c_1705, c_3587])).
% 29.13/18.73  tff(c_3630, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_3620])).
% 29.13/18.73  tff(c_3771, plain, (![B_318]: (r1_tarski(B_318, k2_zfmisc_1(k1_relat_1(B_318), '#skF_3')) | ~v5_relat_1(B_318, '#skF_2') | ~v1_relat_1(B_318))), inference(resolution, [status(thm)], [c_6, c_3547])).
% 29.13/18.73  tff(c_3828, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3')) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1705, c_3771])).
% 29.13/18.73  tff(c_3856, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_226, c_3828])).
% 29.13/18.73  tff(c_1861, plain, (![B_206, C_207, A_208]: (k1_xboole_0=B_206 | v1_funct_2(C_207, A_208, B_206) | k1_relset_1(A_208, B_206, C_207)!=A_208 | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_206))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_4092, plain, (![B_323, A_324, A_325]: (k1_xboole_0=B_323 | v1_funct_2(A_324, A_325, B_323) | k1_relset_1(A_325, B_323, A_324)!=A_325 | ~r1_tarski(A_324, k2_zfmisc_1(A_325, B_323)))), inference(resolution, [status(thm)], [c_24, c_1861])).
% 29.13/18.73  tff(c_4101, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_3856, c_4092])).
% 29.13/18.73  tff(c_4156, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_4101])).
% 29.13/18.73  tff(c_4157, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_151, c_4156])).
% 29.13/18.73  tff(c_83, plain, (![A_42]: (k2_zfmisc_1(A_42, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.13/18.73  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_38])).
% 29.13/18.73  tff(c_4247, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4157, c_87])).
% 29.13/18.73  tff(c_4252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_4247])).
% 29.13/18.73  tff(c_4253, plain, (v1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_187])).
% 29.13/18.73  tff(c_4254, plain, (v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_187])).
% 29.13/18.73  tff(c_4870, plain, (![A_396, B_397, C_398]: (k1_relset_1(A_396, B_397, C_398)=k1_relat_1(C_398) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_396, B_397))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.13/18.73  tff(c_4889, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4870])).
% 29.13/18.73  tff(c_5835, plain, (![B_482, A_483, C_484]: (k1_xboole_0=B_482 | k1_relset_1(A_483, B_482, C_484)=A_483 | ~v1_funct_2(C_484, A_483, B_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_483, B_482))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_5845, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_5835])).
% 29.13/18.73  tff(c_5860, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4889, c_5845])).
% 29.13/18.73  tff(c_5861, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_92, c_5860])).
% 29.13/18.73  tff(c_4272, plain, (![C_328, B_329, A_330]: (v5_relat_1(C_328, B_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_4291, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_4272])).
% 29.13/18.73  tff(c_4622, plain, (![B_377, A_378]: (r1_tarski(k2_relat_1(B_377), A_378) | ~v5_relat_1(B_377, A_378) | ~v1_relat_1(B_377))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_4459, plain, (![A_360, C_361, B_362]: (r1_tarski(A_360, C_361) | ~r1_tarski(B_362, C_361) | ~r1_tarski(A_360, B_362))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.13/18.73  tff(c_4474, plain, (![A_360]: (r1_tarski(A_360, '#skF_3') | ~r1_tarski(A_360, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_4459])).
% 29.13/18.73  tff(c_4662, plain, (![B_377]: (r1_tarski(k2_relat_1(B_377), '#skF_3') | ~v5_relat_1(B_377, '#skF_2') | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_4622, c_4474])).
% 29.13/18.73  tff(c_5433, plain, (![C_453, A_454, B_455]: (m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~r1_tarski(k2_relat_1(C_453), B_455) | ~r1_tarski(k1_relat_1(C_453), A_454) | ~v1_relat_1(C_453))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.13/18.73  tff(c_7203, plain, (![C_556, A_557, B_558]: (r1_tarski(C_556, k2_zfmisc_1(A_557, B_558)) | ~r1_tarski(k2_relat_1(C_556), B_558) | ~r1_tarski(k1_relat_1(C_556), A_557) | ~v1_relat_1(C_556))), inference(resolution, [status(thm)], [c_5433, c_22])).
% 29.13/18.73  tff(c_7346, plain, (![B_565, A_566]: (r1_tarski(B_565, k2_zfmisc_1(A_566, '#skF_3')) | ~r1_tarski(k1_relat_1(B_565), A_566) | ~v5_relat_1(B_565, '#skF_2') | ~v1_relat_1(B_565))), inference(resolution, [status(thm)], [c_4662, c_7203])).
% 29.13/18.73  tff(c_7353, plain, (![A_566]: (r1_tarski('#skF_4', k2_zfmisc_1(A_566, '#skF_3')) | ~r1_tarski('#skF_1', A_566) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5861, c_7346])).
% 29.13/18.73  tff(c_7384, plain, (![A_567]: (r1_tarski('#skF_4', k2_zfmisc_1(A_567, '#skF_3')) | ~r1_tarski('#skF_1', A_567))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_4291, c_7353])).
% 29.13/18.73  tff(c_4888, plain, (![A_396, B_397, A_11]: (k1_relset_1(A_396, B_397, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_396, B_397)))), inference(resolution, [status(thm)], [c_24, c_4870])).
% 29.13/18.73  tff(c_7387, plain, (![A_567]: (k1_relset_1(A_567, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_567))), inference(resolution, [status(thm)], [c_7384, c_4888])).
% 29.13/18.73  tff(c_7420, plain, (![A_568]: (k1_relset_1(A_568, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_568))), inference(demodulation, [status(thm), theory('equality')], [c_5861, c_7387])).
% 29.13/18.73  tff(c_7435, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_7420])).
% 29.13/18.73  tff(c_7440, plain, (![B_569]: (r1_tarski(B_569, k2_zfmisc_1(k1_relat_1(B_569), '#skF_3')) | ~v5_relat_1(B_569, '#skF_2') | ~v1_relat_1(B_569))), inference(resolution, [status(thm)], [c_6, c_7346])).
% 29.13/18.73  tff(c_7488, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3')) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5861, c_7440])).
% 29.13/18.73  tff(c_7513, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_4291, c_7488])).
% 29.13/18.73  tff(c_5565, plain, (![B_460, C_461, A_462]: (k1_xboole_0=B_460 | v1_funct_2(C_461, A_462, B_460) | k1_relset_1(A_462, B_460, C_461)!=A_462 | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_462, B_460))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_7547, plain, (![B_570, A_571, A_572]: (k1_xboole_0=B_570 | v1_funct_2(A_571, A_572, B_570) | k1_relset_1(A_572, B_570, A_571)!=A_572 | ~r1_tarski(A_571, k2_zfmisc_1(A_572, B_570)))), inference(resolution, [status(thm)], [c_24, c_5565])).
% 29.13/18.73  tff(c_7550, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_7513, c_7547])).
% 29.13/18.73  tff(c_7598, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_7550])).
% 29.13/18.73  tff(c_7599, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_151, c_7598])).
% 29.13/18.73  tff(c_7691, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_7599, c_10])).
% 29.13/18.73  tff(c_125, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.13/18.73  tff(c_132, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_125])).
% 29.13/18.73  tff(c_4524, plain, (![A_368]: (r1_tarski(A_368, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_368, '#skF_4'))), inference(resolution, [status(thm)], [c_132, c_4459])).
% 29.13/18.73  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.13/18.73  tff(c_5380, plain, (![A_448, A_449]: (r1_tarski(A_448, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_448, A_449) | ~r1_tarski(A_449, '#skF_4'))), inference(resolution, [status(thm)], [c_4524, c_8])).
% 29.13/18.73  tff(c_5415, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_5380])).
% 29.13/18.73  tff(c_5426, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_5415])).
% 29.13/18.73  tff(c_7773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7691, c_5426])).
% 29.13/18.73  tff(c_7775, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_5415])).
% 29.13/18.73  tff(c_4542, plain, (![A_3, A_368]: (r1_tarski(A_3, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_3, A_368) | ~r1_tarski(A_368, '#skF_4'))), inference(resolution, [status(thm)], [c_4524, c_8])).
% 29.13/18.73  tff(c_7777, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_7775, c_4542])).
% 29.13/18.73  tff(c_7790, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7777])).
% 29.13/18.73  tff(c_4290, plain, (![A_11, B_329, A_330]: (v5_relat_1(A_11, B_329) | ~r1_tarski(A_11, k2_zfmisc_1(A_330, B_329)))), inference(resolution, [status(thm)], [c_24, c_4272])).
% 29.13/18.73  tff(c_7894, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_7790, c_4290])).
% 29.13/18.73  tff(c_4801, plain, (![B_391]: (r1_tarski(k2_relat_1(B_391), '#skF_3') | ~v5_relat_1(B_391, '#skF_2') | ~v1_relat_1(B_391))), inference(resolution, [status(thm)], [c_4622, c_4474])).
% 29.13/18.73  tff(c_34, plain, (![B_22, A_21]: (v5_relat_1(B_22, A_21) | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_4816, plain, (![B_391]: (v5_relat_1(B_391, '#skF_3') | ~v5_relat_1(B_391, '#skF_2') | ~v1_relat_1(B_391))), inference(resolution, [status(thm)], [c_4801, c_34])).
% 29.13/18.73  tff(c_7909, plain, (v5_relat_1('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7894, c_4816])).
% 29.13/18.73  tff(c_7915, plain, (v5_relat_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_7909])).
% 29.13/18.73  tff(c_4823, plain, (![B_392]: (v5_relat_1(B_392, '#skF_3') | ~v5_relat_1(B_392, '#skF_2') | ~v1_relat_1(B_392))), inference(resolution, [status(thm)], [c_4801, c_34])).
% 29.13/18.73  tff(c_4841, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4291, c_4823])).
% 29.13/18.73  tff(c_4852, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_4841])).
% 29.13/18.73  tff(c_7921, plain, (![B_577, A_578, C_579]: (k1_xboole_0=B_577 | k1_relset_1(A_578, B_577, C_579)=A_578 | ~v1_funct_2(C_579, A_578, B_577) | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_578, B_577))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_7931, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_7921])).
% 29.13/18.73  tff(c_7946, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4889, c_7931])).
% 29.13/18.73  tff(c_7947, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_92, c_7946])).
% 29.13/18.73  tff(c_36, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_7838, plain, (![C_574, A_575, B_576]: (m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(A_575, B_576))) | ~r1_tarski(k2_relat_1(C_574), B_576) | ~r1_tarski(k1_relat_1(C_574), A_575) | ~v1_relat_1(C_574))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.13/18.73  tff(c_9672, plain, (![C_659, A_660, B_661]: (r1_tarski(C_659, k2_zfmisc_1(A_660, B_661)) | ~r1_tarski(k2_relat_1(C_659), B_661) | ~r1_tarski(k1_relat_1(C_659), A_660) | ~v1_relat_1(C_659))), inference(resolution, [status(thm)], [c_7838, c_22])).
% 29.13/18.73  tff(c_14393, plain, (![B_852, A_853, A_854]: (r1_tarski(B_852, k2_zfmisc_1(A_853, A_854)) | ~r1_tarski(k1_relat_1(B_852), A_853) | ~v5_relat_1(B_852, A_854) | ~v1_relat_1(B_852))), inference(resolution, [status(thm)], [c_36, c_9672])).
% 29.13/18.73  tff(c_14446, plain, (![B_855, A_856]: (r1_tarski(B_855, k2_zfmisc_1(k1_relat_1(B_855), A_856)) | ~v5_relat_1(B_855, A_856) | ~v1_relat_1(B_855))), inference(resolution, [status(thm)], [c_6, c_14393])).
% 29.13/18.73  tff(c_14532, plain, (![A_856]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', A_856)) | ~v5_relat_1('#skF_4', A_856) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7947, c_14446])).
% 29.13/18.73  tff(c_14578, plain, (![A_857]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', A_857)) | ~v5_relat_1('#skF_4', A_857))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_14532])).
% 29.13/18.73  tff(c_14591, plain, (![A_857]: (k1_relset_1('#skF_1', A_857, '#skF_4')=k1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', A_857))), inference(resolution, [status(thm)], [c_14578, c_4888])).
% 29.13/18.73  tff(c_14630, plain, (![A_858]: (k1_relset_1('#skF_1', A_858, '#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', A_858))), inference(demodulation, [status(thm), theory('equality')], [c_7947, c_14591])).
% 29.13/18.73  tff(c_14749, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_4852, c_14630])).
% 29.13/18.73  tff(c_46, plain, (![C_33, A_31, B_32]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r1_tarski(k2_relat_1(C_33), B_32) | ~r1_tarski(k1_relat_1(C_33), A_31) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.13/18.73  tff(c_8057, plain, (![B_581, C_582, A_583]: (k1_xboole_0=B_581 | v1_funct_2(C_582, A_583, B_581) | k1_relset_1(A_583, B_581, C_582)!=A_583 | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(A_583, B_581))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_11554, plain, (![B_747, C_748, A_749]: (k1_xboole_0=B_747 | v1_funct_2(C_748, A_749, B_747) | k1_relset_1(A_749, B_747, C_748)!=A_749 | ~r1_tarski(k2_relat_1(C_748), B_747) | ~r1_tarski(k1_relat_1(C_748), A_749) | ~v1_relat_1(C_748))), inference(resolution, [status(thm)], [c_46, c_8057])).
% 29.13/18.73  tff(c_20630, plain, (![A_991, B_992, A_993]: (k1_xboole_0=A_991 | v1_funct_2(B_992, A_993, A_991) | k1_relset_1(A_993, A_991, B_992)!=A_993 | ~r1_tarski(k1_relat_1(B_992), A_993) | ~v5_relat_1(B_992, A_991) | ~v1_relat_1(B_992))), inference(resolution, [status(thm)], [c_36, c_11554])).
% 29.13/18.73  tff(c_20674, plain, (![A_991, A_993]: (k1_xboole_0=A_991 | v1_funct_2('#skF_4', A_993, A_991) | k1_relset_1(A_993, A_991, '#skF_4')!=A_993 | ~r1_tarski('#skF_1', A_993) | ~v5_relat_1('#skF_4', A_991) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7947, c_20630])).
% 29.13/18.73  tff(c_76269, plain, (![A_1846, A_1847]: (k1_xboole_0=A_1846 | v1_funct_2('#skF_4', A_1847, A_1846) | k1_relset_1(A_1847, A_1846, '#skF_4')!=A_1847 | ~r1_tarski('#skF_1', A_1847) | ~v5_relat_1('#skF_4', A_1846))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_20674])).
% 29.13/18.73  tff(c_76304, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_76269, c_151])).
% 29.13/18.73  tff(c_76333, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4852, c_6, c_14749, c_76304])).
% 29.13/18.73  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.13/18.73  tff(c_4370, plain, (![C_346, A_347, B_348]: (v4_relat_1(C_346, A_347) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_4415, plain, (![C_353, A_354]: (v4_relat_1(C_353, A_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4370])).
% 29.13/18.73  tff(c_4422, plain, (![A_11, A_354]: (v4_relat_1(A_11, A_354) | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_4415])).
% 29.13/18.73  tff(c_4491, plain, (![A_365, A_366]: (r1_tarski(A_365, A_366) | ~r1_tarski(A_365, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_4459])).
% 29.13/18.73  tff(c_4501, plain, (![B_20, A_366]: (r1_tarski(k1_relat_1(B_20), A_366) | ~v4_relat_1(B_20, k1_xboole_0) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_32, c_4491])).
% 29.13/18.73  tff(c_44, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.13/18.73  tff(c_10504, plain, (![A_701, B_702, C_703]: (k1_relset_1(A_701, B_702, C_703)=k1_relat_1(C_703) | ~r1_tarski(k2_relat_1(C_703), B_702) | ~r1_tarski(k1_relat_1(C_703), A_701) | ~v1_relat_1(C_703))), inference(resolution, [status(thm)], [c_7838, c_44])).
% 29.13/18.73  tff(c_17073, plain, (![A_917, A_918, B_919]: (k1_relset_1(A_917, A_918, B_919)=k1_relat_1(B_919) | ~r1_tarski(k1_relat_1(B_919), A_917) | ~v5_relat_1(B_919, A_918) | ~v1_relat_1(B_919))), inference(resolution, [status(thm)], [c_36, c_10504])).
% 29.13/18.73  tff(c_39035, plain, (![A_1372, A_1373, B_1374]: (k1_relset_1(A_1372, A_1373, B_1374)=k1_relat_1(B_1374) | ~v5_relat_1(B_1374, A_1373) | ~v4_relat_1(B_1374, k1_xboole_0) | ~v1_relat_1(B_1374))), inference(resolution, [status(thm)], [c_4501, c_17073])).
% 29.13/18.73  tff(c_39217, plain, (![A_1372]: (k1_relset_1(A_1372, '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7894, c_39035])).
% 29.13/18.73  tff(c_39466, plain, (![A_1372]: (k1_relset_1(A_1372, '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_39217])).
% 29.13/18.73  tff(c_59015, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_39466])).
% 29.13/18.73  tff(c_59029, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_4422, c_59015])).
% 29.13/18.73  tff(c_4596, plain, (![B_374, A_375]: (v4_relat_1(B_374, A_375) | ~r1_tarski(k1_relat_1(B_374), A_375) | ~v1_relat_1(B_374))), inference(cnfTransformation, [status(thm)], [f_74])).
% 29.13/18.73  tff(c_4615, plain, (![B_374]: (v4_relat_1(B_374, k1_relat_1(B_374)) | ~v1_relat_1(B_374))), inference(resolution, [status(thm)], [c_6, c_4596])).
% 29.13/18.73  tff(c_4388, plain, (![A_11, A_347, B_348]: (v4_relat_1(A_11, A_347) | ~r1_tarski(A_11, k2_zfmisc_1(A_347, B_348)))), inference(resolution, [status(thm)], [c_24, c_4370])).
% 29.13/18.73  tff(c_7893, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_7790, c_4388])).
% 29.13/18.73  tff(c_8529, plain, (![A_603, A_604, B_605]: (r1_tarski(A_603, A_604) | ~r1_tarski(A_603, k1_relat_1(B_605)) | ~v4_relat_1(B_605, A_604) | ~v1_relat_1(B_605))), inference(resolution, [status(thm)], [c_32, c_4459])).
% 29.13/18.73  tff(c_16332, plain, (![B_900, A_901, B_902]: (r1_tarski(k1_relat_1(B_900), A_901) | ~v4_relat_1(B_902, A_901) | ~v1_relat_1(B_902) | ~v4_relat_1(B_900, k1_relat_1(B_902)) | ~v1_relat_1(B_900))), inference(resolution, [status(thm)], [c_32, c_8529])).
% 29.13/18.73  tff(c_16384, plain, (![B_900]: (r1_tarski(k1_relat_1(B_900), '#skF_1') | ~v1_relat_1('#skF_3') | ~v4_relat_1(B_900, k1_relat_1('#skF_3')) | ~v1_relat_1(B_900))), inference(resolution, [status(thm)], [c_7893, c_16332])).
% 29.13/18.73  tff(c_70804, plain, (![B_1793]: (r1_tarski(k1_relat_1(B_1793), '#skF_1') | ~v4_relat_1(B_1793, k1_relat_1('#skF_3')) | ~v1_relat_1(B_1793))), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_16384])).
% 29.13/18.73  tff(c_70900, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4615, c_70804])).
% 29.13/18.73  tff(c_70968, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_70900])).
% 29.13/18.73  tff(c_9705, plain, (![B_22, A_660, A_21]: (r1_tarski(B_22, k2_zfmisc_1(A_660, A_21)) | ~r1_tarski(k1_relat_1(B_22), A_660) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_36, c_9672])).
% 29.13/18.73  tff(c_71000, plain, (![A_21]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', A_21)) | ~v5_relat_1('#skF_3', A_21) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_70968, c_9705])).
% 29.13/18.73  tff(c_72741, plain, (![A_1808]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', A_1808)) | ~v5_relat_1('#skF_3', A_1808))), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_71000])).
% 29.13/18.73  tff(c_72773, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_72741])).
% 29.13/18.73  tff(c_72791, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_59029, c_72773])).
% 29.13/18.73  tff(c_76337, plain, (~v5_relat_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76333, c_72791])).
% 29.13/18.73  tff(c_76468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7915, c_76337])).
% 29.13/18.73  tff(c_76470, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_39466])).
% 29.13/18.73  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.13/18.73  tff(c_9312, plain, (![C_641, B_642]: (m1_subset_1(C_641, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_641), B_642) | ~r1_tarski(k1_relat_1(C_641), k1_xboole_0) | ~v1_relat_1(C_641))), inference(superposition, [status(thm), theory('equality')], [c_18, c_7838])).
% 29.13/18.73  tff(c_9452, plain, (![C_647]: (m1_subset_1(C_647, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_647), k1_xboole_0) | ~v1_relat_1(C_647))), inference(resolution, [status(thm)], [c_6, c_9312])).
% 29.13/18.73  tff(c_9486, plain, (![B_650]: (m1_subset_1(B_650, k1_zfmisc_1(k1_xboole_0)) | ~v4_relat_1(B_650, k1_xboole_0) | ~v1_relat_1(B_650))), inference(resolution, [status(thm)], [c_4501, c_9452])).
% 29.13/18.73  tff(c_9514, plain, (![B_650]: (r1_tarski(B_650, k1_xboole_0) | ~v4_relat_1(B_650, k1_xboole_0) | ~v1_relat_1(B_650))), inference(resolution, [status(thm)], [c_9486, c_22])).
% 29.13/18.73  tff(c_76484, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76470, c_9514])).
% 29.13/18.73  tff(c_76509, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_76484])).
% 29.13/18.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.13/18.73  tff(c_76902, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_76509, c_2])).
% 29.13/18.73  tff(c_76930, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_76902])).
% 29.13/18.73  tff(c_4320, plain, (![C_336, B_337]: (v5_relat_1(C_336, B_337) | ~m1_subset_1(C_336, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4272])).
% 29.13/18.73  tff(c_4327, plain, (![A_11, B_337]: (v5_relat_1(A_11, B_337) | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_4320])).
% 29.13/18.73  tff(c_4472, plain, (![A_360, A_6]: (r1_tarski(A_360, A_6) | ~r1_tarski(A_360, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_4459])).
% 29.13/18.73  tff(c_4663, plain, (![B_377, A_6]: (r1_tarski(k2_relat_1(B_377), A_6) | ~v5_relat_1(B_377, k1_xboole_0) | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_4622, c_4472])).
% 29.13/18.73  tff(c_8211, plain, (![A_587, B_588, A_589]: (k1_relset_1(A_587, B_588, A_589)=k1_relat_1(A_589) | ~r1_tarski(A_589, k2_zfmisc_1(A_587, B_588)))), inference(resolution, [status(thm)], [c_24, c_4870])).
% 29.13/18.73  tff(c_35302, plain, (![A_1325, B_1326, B_1327]: (k1_relset_1(A_1325, B_1326, k2_relat_1(B_1327))=k1_relat_1(k2_relat_1(B_1327)) | ~v5_relat_1(B_1327, k1_xboole_0) | ~v1_relat_1(B_1327))), inference(resolution, [status(thm)], [c_4663, c_8211])).
% 29.13/18.73  tff(c_4408, plain, (![B_350, A_351]: (v5_relat_1(B_350, A_351) | ~r1_tarski(k2_relat_1(B_350), A_351) | ~v1_relat_1(B_350))), inference(cnfTransformation, [status(thm)], [f_80])).
% 29.13/18.73  tff(c_4413, plain, (![B_350]: (v5_relat_1(B_350, k2_relat_1(B_350)) | ~v1_relat_1(B_350))), inference(resolution, [status(thm)], [c_6, c_4408])).
% 29.13/18.73  tff(c_7774, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_5415])).
% 29.13/18.73  tff(c_7817, plain, (v5_relat_1('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7774, c_4290])).
% 29.13/18.73  tff(c_8748, plain, (![A_614, A_615, B_616]: (r1_tarski(A_614, A_615) | ~r1_tarski(A_614, k2_relat_1(B_616)) | ~v5_relat_1(B_616, A_615) | ~v1_relat_1(B_616))), inference(resolution, [status(thm)], [c_4622, c_8])).
% 29.13/18.73  tff(c_16550, plain, (![B_905, A_906, B_907]: (r1_tarski(k2_relat_1(B_905), A_906) | ~v5_relat_1(B_907, A_906) | ~v1_relat_1(B_907) | ~v5_relat_1(B_905, k2_relat_1(B_907)) | ~v1_relat_1(B_905))), inference(resolution, [status(thm)], [c_36, c_8748])).
% 29.13/18.73  tff(c_16624, plain, (![B_905]: (r1_tarski(k2_relat_1(B_905), '#skF_2') | ~v1_relat_1('#skF_2') | ~v5_relat_1(B_905, k2_relat_1('#skF_2')) | ~v1_relat_1(B_905))), inference(resolution, [status(thm)], [c_7817, c_16550])).
% 29.13/18.73  tff(c_33168, plain, (![B_1297]: (r1_tarski(k2_relat_1(B_1297), '#skF_2') | ~v5_relat_1(B_1297, k2_relat_1('#skF_2')) | ~v1_relat_1(B_1297))), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_16624])).
% 29.13/18.73  tff(c_33220, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4413, c_33168])).
% 29.13/18.73  tff(c_33255, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_33220])).
% 29.13/18.73  tff(c_8563, plain, (![A_606]: (r1_tarski(A_606, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_606, '#skF_3'))), inference(resolution, [status(thm)], [c_7790, c_8])).
% 29.13/18.73  tff(c_8600, plain, (![A_3, A_606]: (r1_tarski(A_3, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_3, A_606) | ~r1_tarski(A_606, '#skF_3'))), inference(resolution, [status(thm)], [c_8563, c_8])).
% 29.13/18.73  tff(c_33519, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_33255, c_8600])).
% 29.13/18.73  tff(c_33556, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_33519])).
% 29.13/18.73  tff(c_8079, plain, (![B_581, A_11, A_583]: (k1_xboole_0=B_581 | v1_funct_2(A_11, A_583, B_581) | k1_relset_1(A_583, B_581, A_11)!=A_583 | ~r1_tarski(A_11, k2_zfmisc_1(A_583, B_581)))), inference(resolution, [status(thm)], [c_24, c_8057])).
% 29.13/18.73  tff(c_33708, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_relat_1('#skF_2'), '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', k2_relat_1('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_33556, c_8079])).
% 29.13/18.73  tff(c_33747, plain, (v1_funct_2(k2_relat_1('#skF_2'), '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', k2_relat_1('#skF_2'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_92, c_33708])).
% 29.13/18.73  tff(c_33874, plain, (k1_relset_1('#skF_1', '#skF_2', k2_relat_1('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_33747])).
% 29.13/18.73  tff(c_35308, plain, (k1_relat_1(k2_relat_1('#skF_2'))!='#skF_1' | ~v5_relat_1('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35302, c_33874])).
% 29.13/18.73  tff(c_35363, plain, (k1_relat_1(k2_relat_1('#skF_2'))!='#skF_1' | ~v5_relat_1('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_35308])).
% 29.13/18.73  tff(c_35381, plain, (~v5_relat_1('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_35363])).
% 29.13/18.73  tff(c_35391, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_4327, c_35381])).
% 29.13/18.73  tff(c_76942, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76930, c_35391])).
% 29.13/18.73  tff(c_77054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_76942])).
% 29.13/18.73  tff(c_77056, plain, (v5_relat_1('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_35363])).
% 29.13/18.73  tff(c_9473, plain, (![C_648, A_649]: (m1_subset_1(C_648, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_648), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_648), A_649) | ~v1_relat_1(C_648))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7838])).
% 29.13/18.73  tff(c_13596, plain, (![B_818, A_819]: (m1_subset_1(B_818, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(B_818), A_819) | ~v5_relat_1(B_818, k1_xboole_0) | ~v1_relat_1(B_818))), inference(resolution, [status(thm)], [c_36, c_9473])).
% 29.13/18.73  tff(c_13751, plain, (![B_822]: (m1_subset_1(B_822, k1_zfmisc_1(k1_xboole_0)) | ~v5_relat_1(B_822, k1_xboole_0) | ~v1_relat_1(B_822))), inference(resolution, [status(thm)], [c_6, c_13596])).
% 29.13/18.73  tff(c_13779, plain, (![B_822]: (r1_tarski(B_822, k1_xboole_0) | ~v5_relat_1(B_822, k1_xboole_0) | ~v1_relat_1(B_822))), inference(resolution, [status(thm)], [c_13751, c_22])).
% 29.13/18.73  tff(c_77067, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_77056, c_13779])).
% 29.13/18.73  tff(c_77091, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_77067])).
% 29.13/18.73  tff(c_77125, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_77091, c_2])).
% 29.13/18.73  tff(c_77153, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77125])).
% 29.13/18.73  tff(c_77155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_77153])).
% 29.13/18.73  tff(c_77156, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_72])).
% 29.13/18.73  tff(c_78726, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78709, c_77156])).
% 29.13/18.73  tff(c_78745, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77192, c_78726])).
% 29.13/18.73  tff(c_78747, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_78745])).
% 29.13/18.73  tff(c_78753, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_78747])).
% 29.13/18.73  tff(c_78760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77192, c_77587, c_78753])).
% 29.13/18.73  tff(c_78761, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_78745])).
% 29.13/18.73  tff(c_78798, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_77441, c_78761])).
% 29.13/18.73  tff(c_78808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77192, c_77341, c_78798])).
% 29.13/18.73  tff(c_78809, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 29.13/18.73  tff(c_78812, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78809, c_78809, c_16])).
% 29.13/18.73  tff(c_78810, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 29.13/18.73  tff(c_78819, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78809, c_78810])).
% 29.13/18.73  tff(c_78858, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78812, c_78819, c_66])).
% 29.13/18.73  tff(c_78875, plain, (![A_2012, B_2013]: (r1_tarski(A_2012, B_2013) | ~m1_subset_1(A_2012, k1_zfmisc_1(B_2013)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.13/18.73  tff(c_78882, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_78858, c_78875])).
% 29.13/18.73  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.13/18.73  tff(c_78859, plain, (![A_7]: (A_7='#skF_1' | ~r1_tarski(A_7, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78809, c_78809, c_12])).
% 29.13/18.73  tff(c_78888, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_78882, c_78859])).
% 29.13/18.73  tff(c_20, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.13/18.73  tff(c_78813, plain, (![A_10]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_78809, c_20])).
% 29.13/18.73  tff(c_78901, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_78888, c_78813])).
% 29.13/18.73  tff(c_78839, plain, (![B_9]: (k2_zfmisc_1('#skF_1', B_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78809, c_78809, c_18])).
% 29.13/18.73  tff(c_78899, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78888, c_78888, c_78839])).
% 29.13/18.73  tff(c_79059, plain, (![C_2041, A_2042, B_2043]: (v4_relat_1(C_2041, A_2042) | ~m1_subset_1(C_2041, k1_zfmisc_1(k2_zfmisc_1(A_2042, B_2043))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.13/18.73  tff(c_79125, plain, (![A_2053, A_2054, B_2055]: (v4_relat_1(A_2053, A_2054) | ~r1_tarski(A_2053, k2_zfmisc_1(A_2054, B_2055)))), inference(resolution, [status(thm)], [c_24, c_79059])).
% 29.13/18.73  tff(c_79152, plain, (![A_2054, B_2055]: (v4_relat_1(k2_zfmisc_1(A_2054, B_2055), A_2054))), inference(resolution, [status(thm)], [c_6, c_79125])).
% 29.13/18.73  tff(c_79090, plain, (![B_2047, A_2048]: (r1_tarski(k1_relat_1(B_2047), A_2048) | ~v4_relat_1(B_2047, A_2048) | ~v1_relat_1(B_2047))), inference(cnfTransformation, [status(thm)], [f_74])).
% 29.13/18.73  tff(c_78896, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78888, c_78888, c_78859])).
% 29.13/18.73  tff(c_79173, plain, (![B_2061]: (k1_relat_1(B_2061)='#skF_4' | ~v4_relat_1(B_2061, '#skF_4') | ~v1_relat_1(B_2061))), inference(resolution, [status(thm)], [c_79090, c_78896])).
% 29.13/18.73  tff(c_79177, plain, (![B_2055]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_2055))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_2055)))), inference(resolution, [status(thm)], [c_79152, c_79173])).
% 29.13/18.73  tff(c_79188, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_78899, c_79177])).
% 29.13/18.73  tff(c_79390, plain, (![A_2087, B_2088, C_2089]: (k1_relset_1(A_2087, B_2088, C_2089)=k1_relat_1(C_2089) | ~m1_subset_1(C_2089, k1_zfmisc_1(k2_zfmisc_1(A_2087, B_2088))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.13/18.73  tff(c_79400, plain, (![A_2087, B_2088]: (k1_relset_1(A_2087, B_2088, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_78901, c_79390])).
% 29.13/18.73  tff(c_79406, plain, (![A_2087, B_2088]: (k1_relset_1(A_2087, B_2088, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79188, c_79400])).
% 29.13/18.73  tff(c_78905, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78888, c_78809])).
% 29.13/18.73  tff(c_52, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.13/18.73  tff(c_76, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 29.13/18.73  tff(c_79548, plain, (![C_2100, B_2101]: (v1_funct_2(C_2100, '#skF_4', B_2101) | k1_relset_1('#skF_4', B_2101, C_2100)!='#skF_4' | ~m1_subset_1(C_2100, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78905, c_78905, c_78905, c_78905, c_76])).
% 29.13/18.73  tff(c_79551, plain, (![B_2101]: (v1_funct_2('#skF_4', '#skF_4', B_2101) | k1_relset_1('#skF_4', B_2101, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_78901, c_79548])).
% 29.13/18.73  tff(c_79557, plain, (![B_2101]: (v1_funct_2('#skF_4', '#skF_4', B_2101))), inference(demodulation, [status(thm), theory('equality')], [c_79406, c_79551])).
% 29.13/18.73  tff(c_78915, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78888, c_78888, c_72])).
% 29.13/18.73  tff(c_78916, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_78915])).
% 29.13/18.73  tff(c_79562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79557, c_78916])).
% 29.13/18.73  tff(c_79563, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_78915])).
% 29.13/18.73  tff(c_79637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78901, c_78899, c_79563])).
% 29.13/18.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.13/18.73  
% 29.13/18.73  Inference rules
% 29.13/18.73  ----------------------
% 29.13/18.73  #Ref     : 0
% 29.13/18.73  #Sup     : 15645
% 29.13/18.73  #Fact    : 0
% 29.13/18.73  #Define  : 0
% 29.13/18.73  #Split   : 77
% 29.13/18.73  #Chain   : 0
% 29.13/18.73  #Close   : 0
% 29.13/18.73  
% 29.13/18.73  Ordering : KBO
% 29.13/18.73  
% 29.13/18.73  Simplification rules
% 29.13/18.73  ----------------------
% 29.13/18.73  #Subsume      : 5008
% 29.13/18.73  #Demod        : 13173
% 29.13/18.73  #Tautology    : 3296
% 29.13/18.73  #SimpNegUnit  : 675
% 29.13/18.73  #BackRed      : 646
% 29.13/18.73  
% 29.13/18.73  #Partial instantiations: 0
% 29.13/18.73  #Strategies tried      : 1
% 29.13/18.73  
% 29.13/18.73  Timing (in seconds)
% 29.13/18.73  ----------------------
% 29.13/18.73  Preprocessing        : 0.54
% 29.13/18.73  Parsing              : 0.27
% 29.13/18.73  CNF conversion       : 0.04
% 29.13/18.73  Main loop            : 17.22
% 29.13/18.73  Inferencing          : 2.84
% 29.13/18.73  Reduction            : 8.36
% 29.13/18.73  Demodulation         : 6.80
% 29.13/18.73  BG Simplification    : 0.20
% 29.13/18.73  Subsumption          : 4.73
% 29.13/18.73  Abstraction          : 0.32
% 29.13/18.73  MUC search           : 0.00
% 29.13/18.73  Cooper               : 0.00
% 29.13/18.73  Total                : 17.86
% 29.13/18.73  Index Insertion      : 0.00
% 29.13/18.73  Index Deletion       : 0.00
% 29.13/18.73  Index Matching       : 0.00
% 29.13/18.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
