%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  166 (1467 expanded)
%              Number of leaves         :   39 ( 596 expanded)
%              Depth                    :   16
%              Number of atoms          :  410 (5116 expanded)
%              Number of equality atoms :   52 ( 303 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_118,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,A,A)
            & v3_funct_2(C,A,A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
           => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_69,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_81,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1887,plain,(
    ! [C_178,A_179,B_180] :
      ( v2_funct_1(C_178)
      | ~ v3_funct_2(C_178,A_179,B_180)
      | ~ v1_funct_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1893,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1887])).

tff(c_1897,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1893])).

tff(c_42,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_1790,plain,(
    ! [A_159,B_160,D_161] :
      ( r2_relset_1(A_159,B_160,D_161,D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1795,plain,(
    ! [A_14] : r2_relset_1(A_14,A_14,k6_partfun1(A_14),k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_55,c_1790])).

tff(c_1769,plain,(
    ! [C_150,B_151,A_152] :
      ( v5_relat_1(C_150,B_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1777,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1769])).

tff(c_1798,plain,(
    ! [B_163,A_164] :
      ( k2_relat_1(B_163) = A_164
      | ~ v2_funct_2(B_163,A_164)
      | ~ v5_relat_1(B_163,A_164)
      | ~ v1_relat_1(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1804,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1777,c_1798])).

tff(c_1810,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1804])).

tff(c_1811,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1810])).

tff(c_1843,plain,(
    ! [C_172,B_173,A_174] :
      ( v2_funct_2(C_172,B_173)
      | ~ v3_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1849,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1843])).

tff(c_1853,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1849])).

tff(c_1855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1811,c_1853])).

tff(c_1856,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1810])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1942,plain,(
    ! [A_193,B_194] :
      ( k2_funct_2(A_193,B_194) = k2_funct_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1948,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1942])).

tff(c_1952,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1948])).

tff(c_1929,plain,(
    ! [A_190,B_191] :
      ( v1_funct_1(k2_funct_2(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1935,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1929])).

tff(c_1939,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1935])).

tff(c_1954,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1939])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2087,plain,(
    ! [B_208,E_205,F_206,C_204,A_203,D_207] :
      ( k1_partfun1(A_203,B_208,C_204,D_207,E_205,F_206) = k5_relat_1(E_205,F_206)
      | ~ m1_subset_1(F_206,k1_zfmisc_1(k2_zfmisc_1(C_204,D_207)))
      | ~ v1_funct_1(F_206)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_208)))
      | ~ v1_funct_1(E_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2095,plain,(
    ! [A_203,B_208,E_205] :
      ( k1_partfun1(A_203,B_208,'#skF_1','#skF_1',E_205,'#skF_2') = k5_relat_1(E_205,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_208)))
      | ~ v1_funct_1(E_205) ) ),
    inference(resolution,[status(thm)],[c_48,c_2087])).

tff(c_2115,plain,(
    ! [A_209,B_210,E_211] :
      ( k1_partfun1(A_209,B_210,'#skF_1','#skF_1',E_211,'#skF_2') = k5_relat_1(E_211,'#skF_2')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_1(E_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2095])).

tff(c_2358,plain,(
    ! [A_219,B_220] :
      ( k1_partfun1(A_219,A_219,'#skF_1','#skF_1',k2_funct_2(A_219,B_220),'#skF_2') = k5_relat_1(k2_funct_2(A_219,B_220),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_219,B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_30,c_2115])).

tff(c_2370,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2358])).

tff(c_2384,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1954,c_1952,c_1952,c_1952,c_2370])).

tff(c_183,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    ! [A_14] : r2_relset_1(A_14,A_14,k6_partfun1(A_14),k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_55,c_183])).

tff(c_258,plain,(
    ! [A_88,B_89] :
      ( k2_funct_2(A_88,B_89) = k2_funct_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_264,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_258])).

tff(c_268,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_264])).

tff(c_247,plain,(
    ! [A_86,B_87] :
      ( v1_funct_1(k2_funct_2(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_zfmisc_1(A_86,A_86)))
      | ~ v3_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_253,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_247])).

tff(c_257,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_253])).

tff(c_269,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_257])).

tff(c_297,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_funct_2(A_98,B_99),k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v3_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_327,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_297])).

tff(c_341,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_327])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_368,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_392,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_368])).

tff(c_277,plain,(
    ! [A_92,B_93] :
      ( v3_funct_2(k2_funct_2(A_92,B_93),A_92,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_281,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_277])).

tff(c_285,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_268,c_281])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( v2_funct_1(C_17)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_357,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_341,c_22])).

tff(c_386,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_285,c_357])).

tff(c_20,plain,(
    ! [C_17,B_16,A_15] :
      ( v2_funct_2(C_17,B_16)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_354,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_341,c_20])).

tff(c_383,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_285,c_354])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( v5_relat_1(C_9,B_8)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_389,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_341,c_10])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(B_19) = A_18
      | ~ v2_funct_2(B_19,A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_412,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_389,c_28])).

tff(c_415,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_383,c_412])).

tff(c_287,plain,(
    ! [A_95,B_96] :
      ( v1_funct_2(k2_funct_2(A_95,B_96),A_95,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_291,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_287])).

tff(c_295,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_268,c_291])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( k2_funct_2(A_28,B_29) = k2_funct_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_348,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_341,c_40])).

tff(c_377,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_295,c_285,c_348])).

tff(c_452,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_30])).

tff(c_456,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_295,c_285,c_341,c_452])).

tff(c_192,plain,(
    ! [C_72,A_73,B_74] :
      ( v2_funct_1(C_72)
      | ~ v3_funct_2(C_72,A_73,B_74)
      | ~ v1_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_198,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_192])).

tff(c_202,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_198])).

tff(c_84,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_105,plain,(
    ! [B_51,A_52] :
      ( k2_relat_1(B_51) = A_52
      | ~ v2_funct_2(B_51,A_52)
      | ~ v5_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_111,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_105])).

tff(c_117,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_111])).

tff(c_118,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_158,plain,(
    ! [C_64,B_65,A_66] :
      ( v2_funct_2(C_64,B_65)
      | ~ v3_funct_2(C_64,A_66,B_65)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_158])).

tff(c_168,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_164])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_168])).

tff(c_171,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_393,plain,(
    ! [D_104,C_101,B_105,A_100,F_103,E_102] :
      ( k1_partfun1(A_100,B_105,C_101,D_104,E_102,F_103) = k5_relat_1(E_102,F_103)
      | ~ m1_subset_1(F_103,k1_zfmisc_1(k2_zfmisc_1(C_101,D_104)))
      | ~ v1_funct_1(F_103)
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_105)))
      | ~ v1_funct_1(E_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_401,plain,(
    ! [A_100,B_105,E_102] :
      ( k1_partfun1(A_100,B_105,'#skF_1','#skF_1',E_102,'#skF_2') = k5_relat_1(E_102,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_105)))
      | ~ v1_funct_1(E_102) ) ),
    inference(resolution,[status(thm)],[c_48,c_393])).

tff(c_416,plain,(
    ! [A_106,B_107,E_108] :
      ( k1_partfun1(A_106,B_107,'#skF_1','#skF_1',E_108,'#skF_2') = k5_relat_1(E_108,'#skF_2')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_401])).

tff(c_626,plain,(
    ! [A_117,B_118] :
      ( k1_partfun1(A_117,A_117,'#skF_1','#skF_1',k2_funct_2(A_117,B_118),'#skF_2') = k5_relat_1(k2_funct_2(A_117,B_118),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_30,c_416])).

tff(c_636,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_626])).

tff(c_647,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_269,c_268,c_268,c_268,c_636])).

tff(c_44,plain,(
    ! [A_31,C_34,B_32] :
      ( r2_relset_1(A_31,A_31,C_34,k2_funct_2(A_31,B_32))
      | ~ r2_relset_1(A_31,A_31,k1_partfun1(A_31,A_31,A_31,A_31,B_32,C_34),k6_partfun1(A_31))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(C_34,A_31,A_31)
      | ~ v1_funct_2(C_34,A_31,A_31)
      | ~ v1_funct_1(C_34)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_771,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_44])).

tff(c_775,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2',k2_funct_1(k2_funct_1('#skF_2')))
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_295,c_285,c_341,c_54,c_52,c_50,c_48,c_377,c_771])).

tff(c_1068,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_1103,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1068])).

tff(c_1106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_202,c_188,c_171,c_1103])).

tff(c_1107,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2',k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_16,plain,(
    ! [D_13,C_12,A_10,B_11] :
      ( D_13 = C_12
      | ~ r2_relset_1(A_10,B_11,C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1110,plain,
    ( k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2'
    | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1107,c_16])).

tff(c_1113,plain,(
    k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_456,c_1110])).

tff(c_1202,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_57])).

tff(c_1209,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_269,c_386,c_415,c_1202])).

tff(c_1707,plain,(
    ! [E_143,B_144,A_145,B_142,A_146] :
      ( k1_partfun1(A_145,B_142,A_146,A_146,E_143,k2_funct_2(A_146,B_144)) = k5_relat_1(E_143,k2_funct_2(A_146,B_144))
      | ~ v1_funct_1(k2_funct_2(A_146,B_144))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_142)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_144,A_146,A_146)
      | ~ v1_funct_2(B_144,A_146,A_146)
      | ~ v1_funct_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_30,c_393])).

tff(c_1721,plain,(
    ! [A_146,B_144] :
      ( k1_partfun1('#skF_1','#skF_1',A_146,A_146,'#skF_2',k2_funct_2(A_146,B_144)) = k5_relat_1('#skF_2',k2_funct_2(A_146,B_144))
      | ~ v1_funct_1(k2_funct_2(A_146,B_144))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_144,A_146,A_146)
      | ~ v1_funct_2(B_144,A_146,A_146)
      | ~ v1_funct_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_48,c_1707])).

tff(c_1736,plain,(
    ! [A_147,B_148] :
      ( k1_partfun1('#skF_1','#skF_1',A_147,A_147,'#skF_2',k2_funct_2(A_147,B_148)) = k5_relat_1('#skF_2',k2_funct_2(A_147,B_148))
      | ~ v1_funct_1(k2_funct_2(A_147,B_148))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v3_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1721])).

tff(c_1750,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1736])).

tff(c_1761,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_269,c_268,c_1209,c_268,c_268,c_1750])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_82,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_270,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_82])).

tff(c_1762,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1761,c_270])).

tff(c_1765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_1762])).

tff(c_1766,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1956,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1766])).

tff(c_2444,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2384,c_1956])).

tff(c_2456,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2444])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_1897,c_1795,c_1856,c_2456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.93  
% 4.88/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.93  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.24/1.93  
% 5.24/1.93  %Foreground sorts:
% 5.24/1.93  
% 5.24/1.93  
% 5.24/1.93  %Background operators:
% 5.24/1.93  
% 5.24/1.93  
% 5.24/1.93  %Foreground operators:
% 5.24/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.24/1.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.24/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/1.93  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.24/1.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.24/1.93  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.24/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.24/1.93  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.24/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.24/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.24/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.24/1.93  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.24/1.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.24/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/1.93  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.24/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.24/1.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/1.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.24/1.93  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.24/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.24/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/1.93  
% 5.24/1.96  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.24/1.96  tff(f_152, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.24/1.96  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.24/1.96  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.24/1.96  tff(f_118, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.24/1.96  tff(f_60, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.24/1.96  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.24/1.96  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.24/1.96  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.24/1.96  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.24/1.96  tff(f_116, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.24/1.96  tff(f_96, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.24/1.96  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.24/1.96  tff(f_139, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.24/1.96  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.24/1.96  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.96  tff(c_69, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_75, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_69])).
% 5.24/1.96  tff(c_81, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_75])).
% 5.24/1.96  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.96  tff(c_50, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.96  tff(c_1887, plain, (![C_178, A_179, B_180]: (v2_funct_1(C_178) | ~v3_funct_2(C_178, A_179, B_180) | ~v1_funct_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_1893, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1887])).
% 5.24/1.96  tff(c_1897, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1893])).
% 5.24/1.96  tff(c_42, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.24/1.96  tff(c_18, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.24/1.96  tff(c_55, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 5.24/1.96  tff(c_1790, plain, (![A_159, B_160, D_161]: (r2_relset_1(A_159, B_160, D_161, D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_1795, plain, (![A_14]: (r2_relset_1(A_14, A_14, k6_partfun1(A_14), k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_55, c_1790])).
% 5.24/1.96  tff(c_1769, plain, (![C_150, B_151, A_152]: (v5_relat_1(C_150, B_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.24/1.96  tff(c_1777, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1769])).
% 5.24/1.96  tff(c_1798, plain, (![B_163, A_164]: (k2_relat_1(B_163)=A_164 | ~v2_funct_2(B_163, A_164) | ~v5_relat_1(B_163, A_164) | ~v1_relat_1(B_163))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.24/1.96  tff(c_1804, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1777, c_1798])).
% 5.24/1.96  tff(c_1810, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1804])).
% 5.24/1.96  tff(c_1811, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1810])).
% 5.24/1.96  tff(c_1843, plain, (![C_172, B_173, A_174]: (v2_funct_2(C_172, B_173) | ~v3_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_1849, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1843])).
% 5.24/1.96  tff(c_1853, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1849])).
% 5.24/1.96  tff(c_1855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1811, c_1853])).
% 5.24/1.96  tff(c_1856, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1810])).
% 5.24/1.96  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.24/1.96  tff(c_57, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 5.24/1.96  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.96  tff(c_1942, plain, (![A_193, B_194]: (k2_funct_2(A_193, B_194)=k2_funct_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_1948, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1942])).
% 5.24/1.96  tff(c_1952, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1948])).
% 5.24/1.96  tff(c_1929, plain, (![A_190, B_191]: (v1_funct_1(k2_funct_2(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_1935, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1929])).
% 5.24/1.96  tff(c_1939, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1935])).
% 5.24/1.96  tff(c_1954, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1939])).
% 5.24/1.96  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_2087, plain, (![B_208, E_205, F_206, C_204, A_203, D_207]: (k1_partfun1(A_203, B_208, C_204, D_207, E_205, F_206)=k5_relat_1(E_205, F_206) | ~m1_subset_1(F_206, k1_zfmisc_1(k2_zfmisc_1(C_204, D_207))) | ~v1_funct_1(F_206) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_208))) | ~v1_funct_1(E_205))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.96  tff(c_2095, plain, (![A_203, B_208, E_205]: (k1_partfun1(A_203, B_208, '#skF_1', '#skF_1', E_205, '#skF_2')=k5_relat_1(E_205, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_208))) | ~v1_funct_1(E_205))), inference(resolution, [status(thm)], [c_48, c_2087])).
% 5.24/1.96  tff(c_2115, plain, (![A_209, B_210, E_211]: (k1_partfun1(A_209, B_210, '#skF_1', '#skF_1', E_211, '#skF_2')=k5_relat_1(E_211, '#skF_2') | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_1(E_211))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2095])).
% 5.24/1.96  tff(c_2358, plain, (![A_219, B_220]: (k1_partfun1(A_219, A_219, '#skF_1', '#skF_1', k2_funct_2(A_219, B_220), '#skF_2')=k5_relat_1(k2_funct_2(A_219, B_220), '#skF_2') | ~v1_funct_1(k2_funct_2(A_219, B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(resolution, [status(thm)], [c_30, c_2115])).
% 5.24/1.96  tff(c_2370, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2358])).
% 5.24/1.96  tff(c_2384, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1954, c_1952, c_1952, c_1952, c_2370])).
% 5.24/1.96  tff(c_183, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_188, plain, (![A_14]: (r2_relset_1(A_14, A_14, k6_partfun1(A_14), k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_55, c_183])).
% 5.24/1.96  tff(c_258, plain, (![A_88, B_89]: (k2_funct_2(A_88, B_89)=k2_funct_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_264, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_258])).
% 5.24/1.96  tff(c_268, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_264])).
% 5.24/1.96  tff(c_247, plain, (![A_86, B_87]: (v1_funct_1(k2_funct_2(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(k2_zfmisc_1(A_86, A_86))) | ~v3_funct_2(B_87, A_86, A_86) | ~v1_funct_2(B_87, A_86, A_86) | ~v1_funct_1(B_87))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_253, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_247])).
% 5.24/1.96  tff(c_257, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_253])).
% 5.24/1.96  tff(c_269, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_257])).
% 5.24/1.96  tff(c_297, plain, (![A_98, B_99]: (m1_subset_1(k2_funct_2(A_98, B_99), k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v3_funct_2(B_99, A_98, A_98) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_327, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_268, c_297])).
% 5.24/1.96  tff(c_341, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_327])).
% 5.24/1.96  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_368, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_341, c_2])).
% 5.24/1.96  tff(c_392, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_368])).
% 5.24/1.96  tff(c_277, plain, (![A_92, B_93]: (v3_funct_2(k2_funct_2(A_92, B_93), A_92, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_281, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_277])).
% 5.24/1.96  tff(c_285, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_268, c_281])).
% 5.24/1.96  tff(c_22, plain, (![C_17, A_15, B_16]: (v2_funct_1(C_17) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_357, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_341, c_22])).
% 5.24/1.96  tff(c_386, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_285, c_357])).
% 5.24/1.96  tff(c_20, plain, (![C_17, B_16, A_15]: (v2_funct_2(C_17, B_16) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_354, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_341, c_20])).
% 5.24/1.96  tff(c_383, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_285, c_354])).
% 5.24/1.96  tff(c_10, plain, (![C_9, B_8, A_7]: (v5_relat_1(C_9, B_8) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.24/1.96  tff(c_389, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_341, c_10])).
% 5.24/1.96  tff(c_28, plain, (![B_19, A_18]: (k2_relat_1(B_19)=A_18 | ~v2_funct_2(B_19, A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.24/1.96  tff(c_412, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_389, c_28])).
% 5.24/1.96  tff(c_415, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_383, c_412])).
% 5.24/1.96  tff(c_287, plain, (![A_95, B_96]: (v1_funct_2(k2_funct_2(A_95, B_96), A_95, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.96  tff(c_291, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_287])).
% 5.24/1.96  tff(c_295, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_268, c_291])).
% 5.24/1.96  tff(c_40, plain, (![A_28, B_29]: (k2_funct_2(A_28, B_29)=k2_funct_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_348, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_341, c_40])).
% 5.24/1.96  tff(c_377, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_295, c_285, c_348])).
% 5.24/1.96  tff(c_452, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_30])).
% 5.24/1.96  tff(c_456, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_295, c_285, c_341, c_452])).
% 5.24/1.96  tff(c_192, plain, (![C_72, A_73, B_74]: (v2_funct_1(C_72) | ~v3_funct_2(C_72, A_73, B_74) | ~v1_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_198, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_192])).
% 5.24/1.96  tff(c_202, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_198])).
% 5.24/1.96  tff(c_84, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.24/1.96  tff(c_92, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_84])).
% 5.24/1.96  tff(c_105, plain, (![B_51, A_52]: (k2_relat_1(B_51)=A_52 | ~v2_funct_2(B_51, A_52) | ~v5_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.24/1.96  tff(c_111, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_92, c_105])).
% 5.24/1.96  tff(c_117, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_111])).
% 5.24/1.96  tff(c_118, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_117])).
% 5.24/1.96  tff(c_158, plain, (![C_64, B_65, A_66]: (v2_funct_2(C_64, B_65) | ~v3_funct_2(C_64, A_66, B_65) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_164, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_158])).
% 5.24/1.96  tff(c_168, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_164])).
% 5.24/1.96  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_168])).
% 5.24/1.96  tff(c_171, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_117])).
% 5.24/1.96  tff(c_393, plain, (![D_104, C_101, B_105, A_100, F_103, E_102]: (k1_partfun1(A_100, B_105, C_101, D_104, E_102, F_103)=k5_relat_1(E_102, F_103) | ~m1_subset_1(F_103, k1_zfmisc_1(k2_zfmisc_1(C_101, D_104))) | ~v1_funct_1(F_103) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_105))) | ~v1_funct_1(E_102))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.96  tff(c_401, plain, (![A_100, B_105, E_102]: (k1_partfun1(A_100, B_105, '#skF_1', '#skF_1', E_102, '#skF_2')=k5_relat_1(E_102, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_105))) | ~v1_funct_1(E_102))), inference(resolution, [status(thm)], [c_48, c_393])).
% 5.24/1.96  tff(c_416, plain, (![A_106, B_107, E_108]: (k1_partfun1(A_106, B_107, '#skF_1', '#skF_1', E_108, '#skF_2')=k5_relat_1(E_108, '#skF_2') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_1(E_108))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_401])).
% 5.24/1.96  tff(c_626, plain, (![A_117, B_118]: (k1_partfun1(A_117, A_117, '#skF_1', '#skF_1', k2_funct_2(A_117, B_118), '#skF_2')=k5_relat_1(k2_funct_2(A_117, B_118), '#skF_2') | ~v1_funct_1(k2_funct_2(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(resolution, [status(thm)], [c_30, c_416])).
% 5.24/1.96  tff(c_636, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_626])).
% 5.24/1.96  tff(c_647, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_269, c_268, c_268, c_268, c_636])).
% 5.24/1.96  tff(c_44, plain, (![A_31, C_34, B_32]: (r2_relset_1(A_31, A_31, C_34, k2_funct_2(A_31, B_32)) | ~r2_relset_1(A_31, A_31, k1_partfun1(A_31, A_31, A_31, A_31, B_32, C_34), k6_partfun1(A_31)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(C_34, A_31, A_31) | ~v1_funct_2(C_34, A_31, A_31) | ~v1_funct_1(C_34) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.24/1.96  tff(c_771, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_44])).
% 5.24/1.96  tff(c_775, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_1(k2_funct_1('#skF_2'))) | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_295, c_285, c_341, c_54, c_52, c_50, c_48, c_377, c_771])).
% 5.24/1.96  tff(c_1068, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_775])).
% 5.24/1.96  tff(c_1103, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1068])).
% 5.24/1.96  tff(c_1106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_202, c_188, c_171, c_1103])).
% 5.24/1.96  tff(c_1107, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_775])).
% 5.24/1.96  tff(c_16, plain, (![D_13, C_12, A_10, B_11]: (D_13=C_12 | ~r2_relset_1(A_10, B_11, C_12, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_1110, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2' | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_1107, c_16])).
% 5.24/1.96  tff(c_1113, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_456, c_1110])).
% 5.24/1.96  tff(c_1202, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_57])).
% 5.24/1.96  tff(c_1209, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_269, c_386, c_415, c_1202])).
% 5.24/1.96  tff(c_1707, plain, (![E_143, B_144, A_145, B_142, A_146]: (k1_partfun1(A_145, B_142, A_146, A_146, E_143, k2_funct_2(A_146, B_144))=k5_relat_1(E_143, k2_funct_2(A_146, B_144)) | ~v1_funct_1(k2_funct_2(A_146, B_144)) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_142))) | ~v1_funct_1(E_143) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_144, A_146, A_146) | ~v1_funct_2(B_144, A_146, A_146) | ~v1_funct_1(B_144))), inference(resolution, [status(thm)], [c_30, c_393])).
% 5.24/1.96  tff(c_1721, plain, (![A_146, B_144]: (k1_partfun1('#skF_1', '#skF_1', A_146, A_146, '#skF_2', k2_funct_2(A_146, B_144))=k5_relat_1('#skF_2', k2_funct_2(A_146, B_144)) | ~v1_funct_1(k2_funct_2(A_146, B_144)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_144, A_146, A_146) | ~v1_funct_2(B_144, A_146, A_146) | ~v1_funct_1(B_144))), inference(resolution, [status(thm)], [c_48, c_1707])).
% 5.24/1.96  tff(c_1736, plain, (![A_147, B_148]: (k1_partfun1('#skF_1', '#skF_1', A_147, A_147, '#skF_2', k2_funct_2(A_147, B_148))=k5_relat_1('#skF_2', k2_funct_2(A_147, B_148)) | ~v1_funct_1(k2_funct_2(A_147, B_148)) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v3_funct_2(B_148, A_147, A_147) | ~v1_funct_2(B_148, A_147, A_147) | ~v1_funct_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1721])).
% 5.24/1.96  tff(c_1750, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1736])).
% 5.24/1.96  tff(c_1761, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_269, c_268, c_1209, c_268, c_268, c_1750])).
% 5.24/1.96  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.96  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.24/1.96  tff(c_270, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_82])).
% 5.24/1.96  tff(c_1762, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1761, c_270])).
% 5.24/1.96  tff(c_1765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_1762])).
% 5.24/1.96  tff(c_1766, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 5.24/1.96  tff(c_1956, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1766])).
% 5.24/1.96  tff(c_2444, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2384, c_1956])).
% 5.24/1.96  tff(c_2456, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2444])).
% 5.24/1.96  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_1897, c_1795, c_1856, c_2456])).
% 5.24/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.96  
% 5.24/1.96  Inference rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Ref     : 0
% 5.24/1.96  #Sup     : 496
% 5.24/1.96  #Fact    : 0
% 5.24/1.96  #Define  : 0
% 5.24/1.96  #Split   : 10
% 5.24/1.96  #Chain   : 0
% 5.24/1.96  #Close   : 0
% 5.24/1.96  
% 5.24/1.96  Ordering : KBO
% 5.24/1.96  
% 5.24/1.96  Simplification rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Subsume      : 21
% 5.24/1.96  #Demod        : 1168
% 5.24/1.96  #Tautology    : 216
% 5.24/1.96  #SimpNegUnit  : 3
% 5.24/1.96  #BackRed      : 75
% 5.24/1.96  
% 5.24/1.96  #Partial instantiations: 0
% 5.24/1.96  #Strategies tried      : 1
% 5.24/1.96  
% 5.24/1.96  Timing (in seconds)
% 5.24/1.96  ----------------------
% 5.24/1.97  Preprocessing        : 0.35
% 5.24/1.97  Parsing              : 0.18
% 5.24/1.97  CNF conversion       : 0.02
% 5.24/1.97  Main loop            : 0.82
% 5.24/1.97  Inferencing          : 0.28
% 5.24/1.97  Reduction            : 0.31
% 5.24/1.97  Demodulation         : 0.23
% 5.24/1.97  BG Simplification    : 0.03
% 5.24/1.97  Subsumption          : 0.14
% 5.24/1.97  Abstraction          : 0.04
% 5.24/1.97  MUC search           : 0.00
% 5.24/1.97  Cooper               : 0.00
% 5.24/1.97  Total                : 1.23
% 5.24/1.97  Index Insertion      : 0.00
% 5.24/1.97  Index Deletion       : 0.00
% 5.24/1.97  Index Matching       : 0.00
% 5.24/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
