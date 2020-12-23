%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 5.45s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  166 (1459 expanded)
%              Number of leaves         :   40 ( 594 expanded)
%              Depth                    :   16
%              Number of atoms          :  410 (5110 expanded)
%              Number of equality atoms :   52 ( 297 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_71,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1860,plain,(
    ! [C_177,A_178,B_179] :
      ( v2_funct_1(C_177)
      | ~ v3_funct_2(C_177,A_178,B_179)
      | ~ v1_funct_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1866,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1860])).

tff(c_1870,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1866])).

tff(c_38,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1823,plain,(
    ! [A_170,B_171,D_172] :
      ( r2_relset_1(A_170,B_171,D_172,D_172)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1828,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_1823])).

tff(c_1743,plain,(
    ! [C_148,B_149,A_150] :
      ( v5_relat_1(C_148,B_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1751,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1743])).

tff(c_1755,plain,(
    ! [B_154,A_155] :
      ( k2_relat_1(B_154) = A_155
      | ~ v2_funct_2(B_154,A_155)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1761,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1751,c_1755])).

tff(c_1767,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1761])).

tff(c_1768,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1767])).

tff(c_1808,plain,(
    ! [C_167,B_168,A_169] :
      ( v2_funct_2(C_167,B_168)
      | ~ v3_funct_2(C_167,A_169,B_168)
      | ~ v1_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1814,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1808])).

tff(c_1818,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1814])).

tff(c_1820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1768,c_1818])).

tff(c_1821,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1767])).

tff(c_44,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1914,plain,(
    ! [A_192,B_193] :
      ( k2_funct_2(A_192,B_193) = k2_funct_1(B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_192,A_192)))
      | ~ v3_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1920,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1914])).

tff(c_1924,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1920])).

tff(c_1902,plain,(
    ! [A_189,B_190] :
      ( v1_funct_1(k2_funct_2(A_189,B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1908,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1902])).

tff(c_1912,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1908])).

tff(c_1934,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1924,c_1912])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2062,plain,(
    ! [C_203,A_202,F_205,B_207,E_204,D_206] :
      ( k1_partfun1(A_202,B_207,C_203,D_206,E_204,F_205) = k5_relat_1(E_204,F_205)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(C_203,D_206)))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_207)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2070,plain,(
    ! [A_202,B_207,E_204] :
      ( k1_partfun1(A_202,B_207,'#skF_1','#skF_1',E_204,'#skF_2') = k5_relat_1(E_204,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_207)))
      | ~ v1_funct_1(E_204) ) ),
    inference(resolution,[status(thm)],[c_50,c_2062])).

tff(c_2090,plain,(
    ! [A_208,B_209,E_210] :
      ( k1_partfun1(A_208,B_209,'#skF_1','#skF_1',E_210,'#skF_2') = k5_relat_1(E_210,'#skF_2')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_funct_1(E_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2070])).

tff(c_2342,plain,(
    ! [A_217,B_218] :
      ( k1_partfun1(A_217,A_217,'#skF_1','#skF_1',k2_funct_2(A_217,B_218),'#skF_2') = k5_relat_1(k2_funct_2(A_217,B_218),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_217,B_218))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_28,c_2090])).

tff(c_2354,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2342])).

tff(c_2368,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1934,c_1924,c_1924,c_1924,c_2354])).

tff(c_107,plain,(
    ! [A_52,B_53,D_54] :
      ( r2_relset_1(A_52,B_53,D_54,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_253,plain,(
    ! [A_86,B_87] :
      ( k2_funct_2(A_86,B_87) = k2_funct_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_zfmisc_1(A_86,A_86)))
      | ~ v3_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_259,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_253])).

tff(c_263,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_259])).

tff(c_241,plain,(
    ! [A_83,B_84] :
      ( v1_funct_1(k2_funct_2(A_83,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_247,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_241])).

tff(c_251,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_247])).

tff(c_264,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_251])).

tff(c_291,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(k2_funct_2(A_95,B_96),k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_321,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_291])).

tff(c_335,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_321])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_362,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_335,c_2])).

tff(c_386,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_362])).

tff(c_280,plain,(
    ! [A_91,B_92] :
      ( v3_funct_2(k2_funct_2(A_91,B_92),A_91,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_284,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_280])).

tff(c_288,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_263,c_284])).

tff(c_20,plain,(
    ! [C_16,A_14,B_15] :
      ( v2_funct_1(C_16)
      | ~ v3_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_351,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_335,c_20])).

tff(c_380,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_288,c_351])).

tff(c_18,plain,(
    ! [C_16,B_15,A_14] :
      ( v2_funct_2(C_16,B_15)
      | ~ v3_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_348,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_335,c_18])).

tff(c_377,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_288,c_348])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( v5_relat_1(C_9,B_8)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_382,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_335,c_10])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(B_18) = A_17
      | ~ v2_funct_2(B_18,A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_406,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_382,c_26])).

tff(c_409,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_377,c_406])).

tff(c_271,plain,(
    ! [A_89,B_90] :
      ( v1_funct_2(k2_funct_2(A_89,B_90),A_89,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_275,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_279,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_263,c_275])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( k2_funct_2(A_28,B_29) = k2_funct_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_342,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_335,c_42])).

tff(c_371,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_279,c_288,c_342])).

tff(c_452,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_28])).

tff(c_456,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_279,c_288,c_335,c_452])).

tff(c_204,plain,(
    ! [C_71,A_72,B_73] :
      ( v2_funct_1(C_71)
      | ~ v3_funct_2(C_71,A_72,B_73)
      | ~ v1_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_210,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_204])).

tff(c_214,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_210])).

tff(c_96,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_115,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(B_56) = A_57
      | ~ v2_funct_2(B_56,A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_115])).

tff(c_127,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_121])).

tff(c_128,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_160,plain,(
    ! [C_65,B_66,A_67] :
      ( v2_funct_2(C_65,B_66)
      | ~ v3_funct_2(C_65,A_67,B_66)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_160])).

tff(c_170,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_166])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_170])).

tff(c_173,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_387,plain,(
    ! [E_99,B_102,D_101,F_100,C_98,A_97] :
      ( k1_partfun1(A_97,B_102,C_98,D_101,E_99,F_100) = k5_relat_1(E_99,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_98,D_101)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_102)))
      | ~ v1_funct_1(E_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_395,plain,(
    ! [A_97,B_102,E_99] :
      ( k1_partfun1(A_97,B_102,'#skF_1','#skF_1',E_99,'#skF_2') = k5_relat_1(E_99,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_102)))
      | ~ v1_funct_1(E_99) ) ),
    inference(resolution,[status(thm)],[c_50,c_387])).

tff(c_419,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_1','#skF_1',E_105,'#skF_2') = k5_relat_1(E_105,'#skF_2')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_395])).

tff(c_619,plain,(
    ! [A_114,B_115] :
      ( k1_partfun1(A_114,A_114,'#skF_1','#skF_1',k2_funct_2(A_114,B_115),'#skF_2') = k5_relat_1(k2_funct_2(A_114,B_115),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_114,B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_zfmisc_1(A_114,A_114)))
      | ~ v3_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_28,c_419])).

tff(c_629,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_619])).

tff(c_640,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_264,c_263,c_263,c_263,c_629])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_772,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_640,c_46])).

tff(c_776,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2',k2_funct_1(k2_funct_1('#skF_2')))
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_279,c_288,c_335,c_56,c_54,c_52,c_50,c_371,c_772])).

tff(c_1058,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_776])).

tff(c_1061,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1058])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_214,c_112,c_173,c_1061])).

tff(c_1065,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2',k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_776])).

tff(c_16,plain,(
    ! [D_13,C_12,A_10,B_11] :
      ( D_13 = C_12
      | ~ r2_relset_1(A_10,B_11,C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1068,plain,
    ( k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2'
    | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1065,c_16])).

tff(c_1071,plain,(
    k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_456,c_1068])).

tff(c_1162,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_58])).

tff(c_1168,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_264,c_380,c_409,c_1162])).

tff(c_1672,plain,(
    ! [B_140,A_141,A_138,E_137,B_139] :
      ( k1_partfun1(A_138,B_140,A_141,A_141,E_137,k2_funct_2(A_141,B_139)) = k5_relat_1(E_137,k2_funct_2(A_141,B_139))
      | ~ v1_funct_1(k2_funct_2(A_141,B_139))
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_140)))
      | ~ v1_funct_1(E_137)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_139,A_141,A_141)
      | ~ v1_funct_2(B_139,A_141,A_141)
      | ~ v1_funct_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_28,c_387])).

tff(c_1686,plain,(
    ! [A_141,B_139] :
      ( k1_partfun1('#skF_1','#skF_1',A_141,A_141,'#skF_2',k2_funct_2(A_141,B_139)) = k5_relat_1('#skF_2',k2_funct_2(A_141,B_139))
      | ~ v1_funct_1(k2_funct_2(A_141,B_139))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_139,A_141,A_141)
      | ~ v1_funct_2(B_139,A_141,A_141)
      | ~ v1_funct_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_50,c_1672])).

tff(c_1701,plain,(
    ! [A_142,B_143] :
      ( k1_partfun1('#skF_1','#skF_1',A_142,A_142,'#skF_2',k2_funct_2(A_142,B_143)) = k5_relat_1('#skF_2',k2_funct_2(A_142,B_143))
      | ~ v1_funct_1(k2_funct_2(A_142,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_142,A_142)))
      | ~ v3_funct_2(B_143,A_142,A_142)
      | ~ v1_funct_2(B_143,A_142,A_142)
      | ~ v1_funct_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1686])).

tff(c_1715,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1701])).

tff(c_1726,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_264,c_263,c_1168,c_263,c_263,c_1715])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_265,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_84])).

tff(c_1727,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_265])).

tff(c_1730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1727])).

tff(c_1731,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1935,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1924,c_1731])).

tff(c_2394,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2368,c_1935])).

tff(c_2406,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2394])).

tff(c_2409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_1870,c_1828,c_1821,c_2406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.45/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.08  
% 5.45/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.09  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.45/2.09  
% 5.45/2.09  %Foreground sorts:
% 5.45/2.09  
% 5.45/2.09  
% 5.45/2.09  %Background operators:
% 5.45/2.09  
% 5.45/2.09  
% 5.45/2.09  %Foreground operators:
% 5.45/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.45/2.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.45/2.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.45/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/2.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.45/2.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.45/2.09  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.45/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.45/2.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.45/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.45/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.45/2.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.45/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.45/2.09  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.45/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.45/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.45/2.09  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.45/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.45/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.45/2.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.45/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.45/2.09  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.45/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.45/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.45/2.09  
% 5.45/2.12  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.45/2.12  tff(f_154, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.45/2.12  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.45/2.12  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.45/2.12  tff(f_98, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.45/2.12  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.45/2.12  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.45/2.12  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.45/2.12  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.45/2.12  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.45/2.12  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.45/2.12  tff(f_94, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.45/2.12  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.45/2.12  tff(f_141, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 5.45/2.12  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.45/2.12  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.12  tff(c_71, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.45/2.12  tff(c_77, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.45/2.12  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 5.45/2.12  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.12  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.12  tff(c_1860, plain, (![C_177, A_178, B_179]: (v2_funct_1(C_177) | ~v3_funct_2(C_177, A_178, B_179) | ~v1_funct_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_1866, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1860])).
% 5.45/2.12  tff(c_1870, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1866])).
% 5.45/2.12  tff(c_38, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.45/2.12  tff(c_1823, plain, (![A_170, B_171, D_172]: (r2_relset_1(A_170, B_171, D_172, D_172) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.45/2.12  tff(c_1828, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_1823])).
% 5.45/2.12  tff(c_1743, plain, (![C_148, B_149, A_150]: (v5_relat_1(C_148, B_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.45/2.12  tff(c_1751, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1743])).
% 5.45/2.12  tff(c_1755, plain, (![B_154, A_155]: (k2_relat_1(B_154)=A_155 | ~v2_funct_2(B_154, A_155) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.45/2.12  tff(c_1761, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1751, c_1755])).
% 5.45/2.12  tff(c_1767, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1761])).
% 5.45/2.12  tff(c_1768, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1767])).
% 5.45/2.12  tff(c_1808, plain, (![C_167, B_168, A_169]: (v2_funct_2(C_167, B_168) | ~v3_funct_2(C_167, A_169, B_168) | ~v1_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_1814, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1808])).
% 5.45/2.12  tff(c_1818, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1814])).
% 5.45/2.12  tff(c_1820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1768, c_1818])).
% 5.45/2.12  tff(c_1821, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1767])).
% 5.45/2.12  tff(c_44, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.45/2.12  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.45/2.12  tff(c_58, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 5.45/2.12  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.12  tff(c_1914, plain, (![A_192, B_193]: (k2_funct_2(A_192, B_193)=k2_funct_1(B_193) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_192, A_192))) | ~v3_funct_2(B_193, A_192, A_192) | ~v1_funct_2(B_193, A_192, A_192) | ~v1_funct_1(B_193))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.45/2.12  tff(c_1920, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1914])).
% 5.45/2.12  tff(c_1924, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1920])).
% 5.45/2.12  tff(c_1902, plain, (![A_189, B_190]: (v1_funct_1(k2_funct_2(A_189, B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_1908, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1902])).
% 5.45/2.12  tff(c_1912, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1908])).
% 5.45/2.12  tff(c_1934, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1924, c_1912])).
% 5.45/2.12  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_2062, plain, (![C_203, A_202, F_205, B_207, E_204, D_206]: (k1_partfun1(A_202, B_207, C_203, D_206, E_204, F_205)=k5_relat_1(E_204, F_205) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(C_203, D_206))) | ~v1_funct_1(F_205) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_207))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.45/2.12  tff(c_2070, plain, (![A_202, B_207, E_204]: (k1_partfun1(A_202, B_207, '#skF_1', '#skF_1', E_204, '#skF_2')=k5_relat_1(E_204, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_207))) | ~v1_funct_1(E_204))), inference(resolution, [status(thm)], [c_50, c_2062])).
% 5.45/2.12  tff(c_2090, plain, (![A_208, B_209, E_210]: (k1_partfun1(A_208, B_209, '#skF_1', '#skF_1', E_210, '#skF_2')=k5_relat_1(E_210, '#skF_2') | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_funct_1(E_210))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2070])).
% 5.45/2.12  tff(c_2342, plain, (![A_217, B_218]: (k1_partfun1(A_217, A_217, '#skF_1', '#skF_1', k2_funct_2(A_217, B_218), '#skF_2')=k5_relat_1(k2_funct_2(A_217, B_218), '#skF_2') | ~v1_funct_1(k2_funct_2(A_217, B_218)) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(resolution, [status(thm)], [c_28, c_2090])).
% 5.45/2.12  tff(c_2354, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2342])).
% 5.45/2.12  tff(c_2368, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1934, c_1924, c_1924, c_1924, c_2354])).
% 5.45/2.12  tff(c_107, plain, (![A_52, B_53, D_54]: (r2_relset_1(A_52, B_53, D_54, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.45/2.12  tff(c_112, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_107])).
% 5.45/2.12  tff(c_253, plain, (![A_86, B_87]: (k2_funct_2(A_86, B_87)=k2_funct_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(k2_zfmisc_1(A_86, A_86))) | ~v3_funct_2(B_87, A_86, A_86) | ~v1_funct_2(B_87, A_86, A_86) | ~v1_funct_1(B_87))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.45/2.12  tff(c_259, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_253])).
% 5.45/2.12  tff(c_263, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_259])).
% 5.45/2.12  tff(c_241, plain, (![A_83, B_84]: (v1_funct_1(k2_funct_2(A_83, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_247, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_241])).
% 5.45/2.12  tff(c_251, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_247])).
% 5.45/2.12  tff(c_264, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_251])).
% 5.45/2.12  tff(c_291, plain, (![A_95, B_96]: (m1_subset_1(k2_funct_2(A_95, B_96), k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_321, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_263, c_291])).
% 5.45/2.12  tff(c_335, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_321])).
% 5.45/2.12  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.45/2.12  tff(c_362, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_335, c_2])).
% 5.45/2.12  tff(c_386, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_362])).
% 5.45/2.12  tff(c_280, plain, (![A_91, B_92]: (v3_funct_2(k2_funct_2(A_91, B_92), A_91, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_284, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_280])).
% 5.45/2.12  tff(c_288, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_263, c_284])).
% 5.45/2.12  tff(c_20, plain, (![C_16, A_14, B_15]: (v2_funct_1(C_16) | ~v3_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_351, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_335, c_20])).
% 5.45/2.12  tff(c_380, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_288, c_351])).
% 5.45/2.12  tff(c_18, plain, (![C_16, B_15, A_14]: (v2_funct_2(C_16, B_15) | ~v3_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_348, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_335, c_18])).
% 5.45/2.12  tff(c_377, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_288, c_348])).
% 5.45/2.12  tff(c_10, plain, (![C_9, B_8, A_7]: (v5_relat_1(C_9, B_8) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.45/2.12  tff(c_382, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_335, c_10])).
% 5.45/2.12  tff(c_26, plain, (![B_18, A_17]: (k2_relat_1(B_18)=A_17 | ~v2_funct_2(B_18, A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.45/2.12  tff(c_406, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_382, c_26])).
% 5.45/2.12  tff(c_409, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_386, c_377, c_406])).
% 5.45/2.12  tff(c_271, plain, (![A_89, B_90]: (v1_funct_2(k2_funct_2(A_89, B_90), A_89, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.12  tff(c_275, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_271])).
% 5.45/2.12  tff(c_279, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_263, c_275])).
% 5.45/2.12  tff(c_42, plain, (![A_28, B_29]: (k2_funct_2(A_28, B_29)=k2_funct_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.45/2.12  tff(c_342, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_335, c_42])).
% 5.45/2.12  tff(c_371, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_279, c_288, c_342])).
% 5.45/2.12  tff(c_452, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_28])).
% 5.45/2.12  tff(c_456, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_279, c_288, c_335, c_452])).
% 5.45/2.12  tff(c_204, plain, (![C_71, A_72, B_73]: (v2_funct_1(C_71) | ~v3_funct_2(C_71, A_72, B_73) | ~v1_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_210, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_204])).
% 5.45/2.12  tff(c_214, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_210])).
% 5.45/2.12  tff(c_96, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.45/2.12  tff(c_104, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_96])).
% 5.45/2.12  tff(c_115, plain, (![B_56, A_57]: (k2_relat_1(B_56)=A_57 | ~v2_funct_2(B_56, A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.45/2.12  tff(c_121, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_104, c_115])).
% 5.45/2.12  tff(c_127, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_121])).
% 5.45/2.12  tff(c_128, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_127])).
% 5.45/2.12  tff(c_160, plain, (![C_65, B_66, A_67]: (v2_funct_2(C_65, B_66) | ~v3_funct_2(C_65, A_67, B_66) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.45/2.12  tff(c_166, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_160])).
% 5.45/2.12  tff(c_170, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_166])).
% 5.45/2.12  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_170])).
% 5.45/2.12  tff(c_173, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_127])).
% 5.45/2.12  tff(c_387, plain, (![E_99, B_102, D_101, F_100, C_98, A_97]: (k1_partfun1(A_97, B_102, C_98, D_101, E_99, F_100)=k5_relat_1(E_99, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_98, D_101))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_102))) | ~v1_funct_1(E_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.45/2.12  tff(c_395, plain, (![A_97, B_102, E_99]: (k1_partfun1(A_97, B_102, '#skF_1', '#skF_1', E_99, '#skF_2')=k5_relat_1(E_99, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_102))) | ~v1_funct_1(E_99))), inference(resolution, [status(thm)], [c_50, c_387])).
% 5.45/2.12  tff(c_419, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_1', '#skF_1', E_105, '#skF_2')=k5_relat_1(E_105, '#skF_2') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_395])).
% 5.45/2.12  tff(c_619, plain, (![A_114, B_115]: (k1_partfun1(A_114, A_114, '#skF_1', '#skF_1', k2_funct_2(A_114, B_115), '#skF_2')=k5_relat_1(k2_funct_2(A_114, B_115), '#skF_2') | ~v1_funct_1(k2_funct_2(A_114, B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_zfmisc_1(A_114, A_114))) | ~v3_funct_2(B_115, A_114, A_114) | ~v1_funct_2(B_115, A_114, A_114) | ~v1_funct_1(B_115))), inference(resolution, [status(thm)], [c_28, c_419])).
% 5.45/2.12  tff(c_629, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_619])).
% 5.45/2.12  tff(c_640, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_264, c_263, c_263, c_263, c_629])).
% 5.45/2.12  tff(c_46, plain, (![A_31, C_34, B_32]: (r2_relset_1(A_31, A_31, C_34, k2_funct_2(A_31, B_32)) | ~r2_relset_1(A_31, A_31, k1_partfun1(A_31, A_31, A_31, A_31, B_32, C_34), k6_partfun1(A_31)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(C_34, A_31, A_31) | ~v1_funct_2(C_34, A_31, A_31) | ~v1_funct_1(C_34) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.45/2.12  tff(c_772, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_46])).
% 5.45/2.12  tff(c_776, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_1(k2_funct_1('#skF_2'))) | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_279, c_288, c_335, c_56, c_54, c_52, c_50, c_371, c_772])).
% 5.45/2.12  tff(c_1058, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_776])).
% 5.45/2.12  tff(c_1061, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1058])).
% 5.45/2.12  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_214, c_112, c_173, c_1061])).
% 5.45/2.12  tff(c_1065, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', k2_funct_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_776])).
% 5.45/2.12  tff(c_16, plain, (![D_13, C_12, A_10, B_11]: (D_13=C_12 | ~r2_relset_1(A_10, B_11, C_12, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.45/2.12  tff(c_1068, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2' | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_1065, c_16])).
% 5.45/2.12  tff(c_1071, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_456, c_1068])).
% 5.45/2.12  tff(c_1162, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_58])).
% 5.45/2.12  tff(c_1168, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_264, c_380, c_409, c_1162])).
% 5.45/2.12  tff(c_1672, plain, (![B_140, A_141, A_138, E_137, B_139]: (k1_partfun1(A_138, B_140, A_141, A_141, E_137, k2_funct_2(A_141, B_139))=k5_relat_1(E_137, k2_funct_2(A_141, B_139)) | ~v1_funct_1(k2_funct_2(A_141, B_139)) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_140))) | ~v1_funct_1(E_137) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_139, A_141, A_141) | ~v1_funct_2(B_139, A_141, A_141) | ~v1_funct_1(B_139))), inference(resolution, [status(thm)], [c_28, c_387])).
% 5.45/2.12  tff(c_1686, plain, (![A_141, B_139]: (k1_partfun1('#skF_1', '#skF_1', A_141, A_141, '#skF_2', k2_funct_2(A_141, B_139))=k5_relat_1('#skF_2', k2_funct_2(A_141, B_139)) | ~v1_funct_1(k2_funct_2(A_141, B_139)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_139, A_141, A_141) | ~v1_funct_2(B_139, A_141, A_141) | ~v1_funct_1(B_139))), inference(resolution, [status(thm)], [c_50, c_1672])).
% 5.45/2.12  tff(c_1701, plain, (![A_142, B_143]: (k1_partfun1('#skF_1', '#skF_1', A_142, A_142, '#skF_2', k2_funct_2(A_142, B_143))=k5_relat_1('#skF_2', k2_funct_2(A_142, B_143)) | ~v1_funct_1(k2_funct_2(A_142, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_142, A_142))) | ~v3_funct_2(B_143, A_142, A_142) | ~v1_funct_2(B_143, A_142, A_142) | ~v1_funct_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1686])).
% 5.45/2.12  tff(c_1715, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1701])).
% 5.45/2.12  tff(c_1726, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_264, c_263, c_1168, c_263, c_263, c_1715])).
% 5.45/2.12  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.12  tff(c_84, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.45/2.12  tff(c_265, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_84])).
% 5.45/2.12  tff(c_1727, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_265])).
% 5.45/2.12  tff(c_1730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_1727])).
% 5.45/2.12  tff(c_1731, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 5.45/2.12  tff(c_1935, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1924, c_1731])).
% 5.45/2.12  tff(c_2394, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2368, c_1935])).
% 5.45/2.12  tff(c_2406, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2394])).
% 5.45/2.12  tff(c_2409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_1870, c_1828, c_1821, c_2406])).
% 5.45/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.12  
% 5.45/2.12  Inference rules
% 5.45/2.12  ----------------------
% 5.45/2.12  #Ref     : 0
% 5.45/2.12  #Sup     : 485
% 5.45/2.12  #Fact    : 0
% 5.45/2.12  #Define  : 0
% 5.45/2.12  #Split   : 9
% 5.45/2.12  #Chain   : 0
% 5.45/2.12  #Close   : 0
% 5.45/2.12  
% 5.45/2.12  Ordering : KBO
% 5.45/2.12  
% 5.45/2.12  Simplification rules
% 5.45/2.12  ----------------------
% 5.45/2.12  #Subsume      : 20
% 5.45/2.12  #Demod        : 1089
% 5.45/2.12  #Tautology    : 207
% 5.45/2.12  #SimpNegUnit  : 3
% 5.45/2.12  #BackRed      : 79
% 5.45/2.12  
% 5.45/2.12  #Partial instantiations: 0
% 5.45/2.12  #Strategies tried      : 1
% 5.45/2.12  
% 5.45/2.12  Timing (in seconds)
% 5.45/2.12  ----------------------
% 5.85/2.13  Preprocessing        : 0.37
% 5.85/2.13  Parsing              : 0.20
% 5.85/2.13  CNF conversion       : 0.02
% 5.85/2.13  Main loop            : 0.95
% 5.85/2.13  Inferencing          : 0.31
% 5.85/2.13  Reduction            : 0.36
% 5.85/2.13  Demodulation         : 0.27
% 5.85/2.13  BG Simplification    : 0.03
% 5.85/2.13  Subsumption          : 0.16
% 5.85/2.13  Abstraction          : 0.04
% 5.85/2.13  MUC search           : 0.00
% 5.85/2.13  Cooper               : 0.00
% 5.85/2.13  Total                : 1.39
% 5.85/2.13  Index Insertion      : 0.00
% 5.85/2.13  Index Deletion       : 0.00
% 5.85/2.13  Index Matching       : 0.00
% 5.85/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
