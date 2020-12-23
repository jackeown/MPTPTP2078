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
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 344 expanded)
%              Number of leaves         :   40 ( 148 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 (1053 expanded)
%              Number of equality atoms :   41 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_95,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_68,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1918,plain,(
    ! [C_191,A_192,B_193] :
      ( v2_funct_1(C_191)
      | ~ v3_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1924,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1918])).

tff(c_1928,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1924])).

tff(c_42,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_1791,plain,(
    ! [A_168,B_169,D_170] :
      ( r2_relset_1(A_168,B_169,D_170,D_170)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1796,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_55,c_1791])).

tff(c_1770,plain,(
    ! [C_159,B_160,A_161] :
      ( v5_relat_1(C_159,B_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1778,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1770])).

tff(c_1799,plain,(
    ! [B_172,A_173] :
      ( k2_relat_1(B_172) = A_173
      | ~ v2_funct_2(B_172,A_173)
      | ~ v5_relat_1(B_172,A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1805,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1778,c_1799])).

tff(c_1811,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1805])).

tff(c_1825,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1811])).

tff(c_1865,plain,(
    ! [C_184,B_185,A_186] :
      ( v2_funct_2(C_184,B_185)
      | ~ v3_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1871,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1865])).

tff(c_1875,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1871])).

tff(c_1877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_1875])).

tff(c_1878,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1811])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1993,plain,(
    ! [A_208,B_209] :
      ( k2_funct_2(A_208,B_209) = k2_funct_1(B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_zfmisc_1(A_208,A_208)))
      | ~ v3_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1999,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1993])).

tff(c_2003,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1999])).

tff(c_1982,plain,(
    ! [A_206,B_207] :
      ( v1_funct_1(k2_funct_2(A_206,B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1988,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1982])).

tff(c_1992,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1988])).

tff(c_2004,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_1992])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2150,plain,(
    ! [A_225,F_221,E_222,C_220,D_224,B_223] :
      ( k1_partfun1(A_225,B_223,C_220,D_224,E_222,F_221) = k5_relat_1(E_222,F_221)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(C_220,D_224)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2158,plain,(
    ! [A_225,B_223,E_222] :
      ( k1_partfun1(A_225,B_223,'#skF_1','#skF_1',E_222,'#skF_2') = k5_relat_1(E_222,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_48,c_2150])).

tff(c_2173,plain,(
    ! [A_226,B_227,E_228] :
      ( k1_partfun1(A_226,B_227,'#skF_1','#skF_1',E_228,'#skF_2') = k5_relat_1(E_228,'#skF_2')
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2158])).

tff(c_2406,plain,(
    ! [A_236,B_237] :
      ( k1_partfun1(A_236,A_236,'#skF_1','#skF_1',k2_funct_2(A_236,B_237),'#skF_2') = k5_relat_1(k2_funct_2(A_236,B_237),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_236,B_237))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(k2_zfmisc_1(A_236,A_236)))
      | ~ v3_funct_2(B_237,A_236,A_236)
      | ~ v1_funct_2(B_237,A_236,A_236)
      | ~ v1_funct_1(B_237) ) ),
    inference(resolution,[status(thm)],[c_30,c_2173])).

tff(c_2416,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2406])).

tff(c_2427,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2004,c_2003,c_2003,c_2003,c_2416])).

tff(c_249,plain,(
    ! [C_80,A_81,B_82] :
      ( v2_funct_1(C_80)
      | ~ v3_funct_2(C_80,A_81,B_82)
      | ~ v1_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_255,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_249])).

tff(c_259,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_255])).

tff(c_199,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_204,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_55,c_199])).

tff(c_209,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_217,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_209])).

tff(c_273,plain,(
    ! [A_88,B_89] :
      ( k1_relset_1(A_88,A_88,B_89) = A_88
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_279,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_273])).

tff(c_284,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_217,c_279])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_319,plain,(
    ! [A_97,B_98] :
      ( k2_funct_2(A_97,B_98) = k2_funct_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_325,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_319])).

tff(c_329,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_325])).

tff(c_308,plain,(
    ! [A_95,B_96] :
      ( v1_funct_1(k2_funct_2(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_314,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_308])).

tff(c_318,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_314])).

tff(c_330,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_318])).

tff(c_468,plain,(
    ! [E_111,C_109,F_110,D_113,A_114,B_112] :
      ( k1_partfun1(A_114,B_112,C_109,D_113,E_111,F_110) = k5_relat_1(E_111,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_109,D_113)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_114,B_112)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1679,plain,(
    ! [A_152,A_155,B_156,E_153,B_154] :
      ( k1_partfun1(A_155,B_156,A_152,A_152,E_153,k2_funct_2(A_152,B_154)) = k5_relat_1(E_153,k2_funct_2(A_152,B_154))
      | ~ v1_funct_1(k2_funct_2(A_152,B_154))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v3_funct_2(B_154,A_152,A_152)
      | ~ v1_funct_2(B_154,A_152,A_152)
      | ~ v1_funct_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_30,c_468])).

tff(c_1695,plain,(
    ! [A_152,B_154] :
      ( k1_partfun1('#skF_1','#skF_1',A_152,A_152,'#skF_2',k2_funct_2(A_152,B_154)) = k5_relat_1('#skF_2',k2_funct_2(A_152,B_154))
      | ~ v1_funct_1(k2_funct_2(A_152,B_154))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v3_funct_2(B_154,A_152,A_152)
      | ~ v1_funct_2(B_154,A_152,A_152)
      | ~ v1_funct_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_48,c_1679])).

tff(c_1716,plain,(
    ! [A_157,B_158] :
      ( k1_partfun1('#skF_1','#skF_1',A_157,A_157,'#skF_2',k2_funct_2(A_157,B_158)) = k5_relat_1('#skF_2',k2_funct_2(A_157,B_158))
      | ~ v1_funct_1(k2_funct_2(A_157,B_158))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v3_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_1(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1695])).

tff(c_1732,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1716])).

tff(c_1752,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_330,c_329,c_329,c_329,c_1732])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_331,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_78])).

tff(c_1757,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_331])).

tff(c_1764,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1757])).

tff(c_1767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_259,c_204,c_284,c_1764])).

tff(c_1768,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2006,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_1768])).

tff(c_2456,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2427,c_2006])).

tff(c_2463,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2456])).

tff(c_2466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_1928,c_1796,c_1878,c_2463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.96  
% 5.12/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.96  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.12/1.96  
% 5.12/1.96  %Foreground sorts:
% 5.12/1.96  
% 5.12/1.96  
% 5.12/1.96  %Background operators:
% 5.12/1.96  
% 5.12/1.96  
% 5.12/1.96  %Foreground operators:
% 5.12/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.12/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.12/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.12/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.12/1.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.12/1.96  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.12/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.12/1.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.12/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.12/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.12/1.96  tff('#skF_1', type, '#skF_1': $i).
% 5.12/1.96  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.12/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.12/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.12/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.12/1.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.12/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.12/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.12/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.12/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.12/1.96  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.12/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.12/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.12/1.96  
% 5.41/1.99  tff(f_138, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.41/1.99  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.41/1.99  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.41/1.99  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.41/1.99  tff(f_59, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.41/1.99  tff(f_57, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.41/1.99  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.41/1.99  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.41/1.99  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.41/1.99  tff(f_115, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.41/1.99  tff(f_95, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.41/1.99  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.41/1.99  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.41/1.99  tff(f_125, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.41/1.99  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/1.99  tff(c_68, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.41/1.99  tff(c_76, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 5.41/1.99  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/1.99  tff(c_50, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/1.99  tff(c_1918, plain, (![C_191, A_192, B_193]: (v2_funct_1(C_191) | ~v3_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.41/1.99  tff(c_1924, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1918])).
% 5.41/1.99  tff(c_1928, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1924])).
% 5.41/1.99  tff(c_42, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/1.99  tff(c_18, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.41/1.99  tff(c_55, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 5.41/1.99  tff(c_1791, plain, (![A_168, B_169, D_170]: (r2_relset_1(A_168, B_169, D_170, D_170) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.41/1.99  tff(c_1796, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_55, c_1791])).
% 5.41/1.99  tff(c_1770, plain, (![C_159, B_160, A_161]: (v5_relat_1(C_159, B_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.41/1.99  tff(c_1778, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1770])).
% 5.41/1.99  tff(c_1799, plain, (![B_172, A_173]: (k2_relat_1(B_172)=A_173 | ~v2_funct_2(B_172, A_173) | ~v5_relat_1(B_172, A_173) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.41/1.99  tff(c_1805, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1778, c_1799])).
% 5.41/1.99  tff(c_1811, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1805])).
% 5.41/1.99  tff(c_1825, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1811])).
% 5.41/1.99  tff(c_1865, plain, (![C_184, B_185, A_186]: (v2_funct_2(C_184, B_185) | ~v3_funct_2(C_184, A_186, B_185) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.41/1.99  tff(c_1871, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1865])).
% 5.41/1.99  tff(c_1875, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1871])).
% 5.41/1.99  tff(c_1877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1825, c_1875])).
% 5.41/1.99  tff(c_1878, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1811])).
% 5.41/1.99  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.41/1.99  tff(c_57, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 5.41/1.99  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/1.99  tff(c_1993, plain, (![A_208, B_209]: (k2_funct_2(A_208, B_209)=k2_funct_1(B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_zfmisc_1(A_208, A_208))) | ~v3_funct_2(B_209, A_208, A_208) | ~v1_funct_2(B_209, A_208, A_208) | ~v1_funct_1(B_209))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.41/1.99  tff(c_1999, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1993])).
% 5.41/1.99  tff(c_2003, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1999])).
% 5.41/1.99  tff(c_1982, plain, (![A_206, B_207]: (v1_funct_1(k2_funct_2(A_206, B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.41/1.99  tff(c_1988, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1982])).
% 5.41/1.99  tff(c_1992, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1988])).
% 5.41/1.99  tff(c_2004, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_1992])).
% 5.41/1.99  tff(c_30, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.41/1.99  tff(c_2150, plain, (![A_225, F_221, E_222, C_220, D_224, B_223]: (k1_partfun1(A_225, B_223, C_220, D_224, E_222, F_221)=k5_relat_1(E_222, F_221) | ~m1_subset_1(F_221, k1_zfmisc_1(k2_zfmisc_1(C_220, D_224))) | ~v1_funct_1(F_221) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.41/1.99  tff(c_2158, plain, (![A_225, B_223, E_222]: (k1_partfun1(A_225, B_223, '#skF_1', '#skF_1', E_222, '#skF_2')=k5_relat_1(E_222, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_48, c_2150])).
% 5.41/1.99  tff(c_2173, plain, (![A_226, B_227, E_228]: (k1_partfun1(A_226, B_227, '#skF_1', '#skF_1', E_228, '#skF_2')=k5_relat_1(E_228, '#skF_2') | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_1(E_228))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2158])).
% 5.41/1.99  tff(c_2406, plain, (![A_236, B_237]: (k1_partfun1(A_236, A_236, '#skF_1', '#skF_1', k2_funct_2(A_236, B_237), '#skF_2')=k5_relat_1(k2_funct_2(A_236, B_237), '#skF_2') | ~v1_funct_1(k2_funct_2(A_236, B_237)) | ~m1_subset_1(B_237, k1_zfmisc_1(k2_zfmisc_1(A_236, A_236))) | ~v3_funct_2(B_237, A_236, A_236) | ~v1_funct_2(B_237, A_236, A_236) | ~v1_funct_1(B_237))), inference(resolution, [status(thm)], [c_30, c_2173])).
% 5.41/1.99  tff(c_2416, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2406])).
% 5.41/1.99  tff(c_2427, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2004, c_2003, c_2003, c_2003, c_2416])).
% 5.41/1.99  tff(c_249, plain, (![C_80, A_81, B_82]: (v2_funct_1(C_80) | ~v3_funct_2(C_80, A_81, B_82) | ~v1_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.41/1.99  tff(c_255, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_249])).
% 5.41/1.99  tff(c_259, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_255])).
% 5.41/1.99  tff(c_199, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.41/1.99  tff(c_204, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_55, c_199])).
% 5.41/1.99  tff(c_209, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.41/1.99  tff(c_217, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_209])).
% 5.41/1.99  tff(c_273, plain, (![A_88, B_89]: (k1_relset_1(A_88, A_88, B_89)=A_88 | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/1.99  tff(c_279, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_273])).
% 5.41/1.99  tff(c_284, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_217, c_279])).
% 5.41/1.99  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.41/1.99  tff(c_56, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 5.41/1.99  tff(c_319, plain, (![A_97, B_98]: (k2_funct_2(A_97, B_98)=k2_funct_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.41/1.99  tff(c_325, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_319])).
% 5.41/1.99  tff(c_329, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_325])).
% 5.41/1.99  tff(c_308, plain, (![A_95, B_96]: (v1_funct_1(k2_funct_2(A_95, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.41/1.99  tff(c_314, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_308])).
% 5.41/1.99  tff(c_318, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_314])).
% 5.41/1.99  tff(c_330, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_318])).
% 5.41/1.99  tff(c_468, plain, (![E_111, C_109, F_110, D_113, A_114, B_112]: (k1_partfun1(A_114, B_112, C_109, D_113, E_111, F_110)=k5_relat_1(E_111, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_109, D_113))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_114, B_112))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.41/1.99  tff(c_1679, plain, (![A_152, A_155, B_156, E_153, B_154]: (k1_partfun1(A_155, B_156, A_152, A_152, E_153, k2_funct_2(A_152, B_154))=k5_relat_1(E_153, k2_funct_2(A_152, B_154)) | ~v1_funct_1(k2_funct_2(A_152, B_154)) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_1(E_153) | ~m1_subset_1(B_154, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v3_funct_2(B_154, A_152, A_152) | ~v1_funct_2(B_154, A_152, A_152) | ~v1_funct_1(B_154))), inference(resolution, [status(thm)], [c_30, c_468])).
% 5.41/1.99  tff(c_1695, plain, (![A_152, B_154]: (k1_partfun1('#skF_1', '#skF_1', A_152, A_152, '#skF_2', k2_funct_2(A_152, B_154))=k5_relat_1('#skF_2', k2_funct_2(A_152, B_154)) | ~v1_funct_1(k2_funct_2(A_152, B_154)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_154, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v3_funct_2(B_154, A_152, A_152) | ~v1_funct_2(B_154, A_152, A_152) | ~v1_funct_1(B_154))), inference(resolution, [status(thm)], [c_48, c_1679])).
% 5.41/1.99  tff(c_1716, plain, (![A_157, B_158]: (k1_partfun1('#skF_1', '#skF_1', A_157, A_157, '#skF_2', k2_funct_2(A_157, B_158))=k5_relat_1('#skF_2', k2_funct_2(A_157, B_158)) | ~v1_funct_1(k2_funct_2(A_157, B_158)) | ~m1_subset_1(B_158, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v3_funct_2(B_158, A_157, A_157) | ~v1_funct_2(B_158, A_157, A_157) | ~v1_funct_1(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1695])).
% 5.41/1.99  tff(c_1732, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1716])).
% 5.41/1.99  tff(c_1752, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_330, c_329, c_329, c_329, c_1732])).
% 5.41/1.99  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/1.99  tff(c_78, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.41/1.99  tff(c_331, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_78])).
% 5.41/1.99  tff(c_1757, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_331])).
% 5.41/1.99  tff(c_1764, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_1757])).
% 5.41/1.99  tff(c_1767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_259, c_204, c_284, c_1764])).
% 5.41/1.99  tff(c_1768, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 5.41/1.99  tff(c_2006, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_1768])).
% 5.41/1.99  tff(c_2456, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2427, c_2006])).
% 5.41/1.99  tff(c_2463, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2456])).
% 5.41/1.99  tff(c_2466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_1928, c_1796, c_1878, c_2463])).
% 5.41/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/1.99  
% 5.41/1.99  Inference rules
% 5.41/1.99  ----------------------
% 5.41/1.99  #Ref     : 0
% 5.41/1.99  #Sup     : 520
% 5.41/1.99  #Fact    : 0
% 5.41/1.99  #Define  : 0
% 5.41/1.99  #Split   : 4
% 5.41/1.99  #Chain   : 0
% 5.41/1.99  #Close   : 0
% 5.41/1.99  
% 5.41/1.99  Ordering : KBO
% 5.41/1.99  
% 5.41/1.99  Simplification rules
% 5.41/1.99  ----------------------
% 5.41/1.99  #Subsume      : 1
% 5.41/1.99  #Demod        : 1222
% 5.41/1.99  #Tautology    : 217
% 5.41/1.99  #SimpNegUnit  : 2
% 5.41/1.99  #BackRed      : 49
% 5.41/1.99  
% 5.41/1.99  #Partial instantiations: 0
% 5.41/1.99  #Strategies tried      : 1
% 5.41/1.99  
% 5.41/1.99  Timing (in seconds)
% 5.41/1.99  ----------------------
% 5.41/1.99  Preprocessing        : 0.33
% 5.41/1.99  Parsing              : 0.17
% 5.41/1.99  CNF conversion       : 0.02
% 5.41/1.99  Main loop            : 0.81
% 5.41/1.99  Inferencing          : 0.28
% 5.41/1.99  Reduction            : 0.30
% 5.41/1.99  Demodulation         : 0.23
% 5.41/1.99  BG Simplification    : 0.03
% 5.41/1.99  Subsumption          : 0.15
% 5.41/1.99  Abstraction          : 0.04
% 5.41/1.99  MUC search           : 0.00
% 5.41/1.99  Cooper               : 0.00
% 5.41/1.99  Total                : 1.19
% 5.41/1.99  Index Insertion      : 0.00
% 5.41/1.99  Index Deletion       : 0.00
% 5.41/1.99  Index Matching       : 0.00
% 5.41/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
