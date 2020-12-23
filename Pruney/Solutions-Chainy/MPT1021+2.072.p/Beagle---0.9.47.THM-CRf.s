%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 351 expanded)
%              Number of leaves         :   42 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 (1073 expanded)
%              Number of equality atoms :   41 (  84 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_62,axiom,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_98,axiom,(
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

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_85,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1934,plain,(
    ! [C_201,A_202,B_203] :
      ( v2_funct_1(C_201)
      | ~ v3_funct_2(C_201,A_202,B_203)
      | ~ v1_funct_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1940,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1934])).

tff(c_1944,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1940])).

tff(c_40,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1913,plain,(
    ! [A_194,B_195,D_196] :
      ( r2_relset_1(A_194,B_195,D_196,D_196)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1918,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_40,c_1913])).

tff(c_1800,plain,(
    ! [C_167,B_168,A_169] :
      ( v5_relat_1(C_167,B_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1808,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1800])).

tff(c_1812,plain,(
    ! [B_173,A_174] :
      ( k2_relat_1(B_173) = A_174
      | ~ v2_funct_2(B_173,A_174)
      | ~ v5_relat_1(B_173,A_174)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1818,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1808,c_1812])).

tff(c_1824,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1818])).

tff(c_1825,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1824])).

tff(c_1887,plain,(
    ! [C_190,B_191,A_192] :
      ( v2_funct_2(C_190,B_191)
      | ~ v3_funct_2(C_190,A_192,B_191)
      | ~ v1_funct_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1893,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1887])).

tff(c_1897,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1893])).

tff(c_1899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_1897])).

tff(c_1900,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_46,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2037,plain,(
    ! [A_222,B_223] :
      ( k2_funct_2(A_222,B_223) = k2_funct_1(B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2043,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2037])).

tff(c_2047,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2043])).

tff(c_2025,plain,(
    ! [A_219,B_220] :
      ( v1_funct_1(k2_funct_2(A_219,B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2031,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2025])).

tff(c_2035,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2031])).

tff(c_2048,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2047,c_2035])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_funct_2(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v3_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2202,plain,(
    ! [F_235,A_233,C_234,D_232,B_236,E_237] :
      ( k1_partfun1(A_233,B_236,C_234,D_232,E_237,F_235) = k5_relat_1(E_237,F_235)
      | ~ m1_subset_1(F_235,k1_zfmisc_1(k2_zfmisc_1(C_234,D_232)))
      | ~ v1_funct_1(F_235)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2210,plain,(
    ! [A_233,B_236,E_237] :
      ( k1_partfun1(A_233,B_236,'#skF_1','#skF_1',E_237,'#skF_2') = k5_relat_1(E_237,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_52,c_2202])).

tff(c_2239,plain,(
    ! [A_238,B_239,E_240] :
      ( k1_partfun1(A_238,B_239,'#skF_1','#skF_1',E_240,'#skF_2') = k5_relat_1(E_240,'#skF_2')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_1(E_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2210])).

tff(c_2490,plain,(
    ! [A_245,B_246] :
      ( k1_partfun1(A_245,A_245,'#skF_1','#skF_1',k2_funct_2(A_245,B_246),'#skF_2') = k5_relat_1(k2_funct_2(A_245,B_246),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_245,B_246))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_zfmisc_1(A_245,A_245)))
      | ~ v3_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_30,c_2239])).

tff(c_2502,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2490])).

tff(c_2516,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2048,c_2047,c_2047,c_2047,c_2502])).

tff(c_258,plain,(
    ! [C_84,A_85,B_86] :
      ( v2_funct_1(C_84)
      | ~ v3_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_258])).

tff(c_268,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_264])).

tff(c_209,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_relset_1(A_73,B_74,D_75,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_214,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_218,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_226,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_218])).

tff(c_282,plain,(
    ! [A_92,B_93] :
      ( k1_relset_1(A_92,A_92,B_93) = A_92
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_288,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_282])).

tff(c_293,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_226,c_288])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_329,plain,(
    ! [A_102,B_103] :
      ( k2_funct_2(A_102,B_103) = k2_funct_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_335,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_329])).

tff(c_339,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_335])).

tff(c_317,plain,(
    ! [A_99,B_100] :
      ( v1_funct_1(k2_funct_2(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_323,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_317])).

tff(c_327,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_323])).

tff(c_340,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_327])).

tff(c_481,plain,(
    ! [C_115,F_116,D_113,E_118,A_114,B_117] :
      ( k1_partfun1(A_114,B_117,C_115,D_113,E_118,F_116) = k5_relat_1(E_118,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_115,D_113)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_114,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1699,plain,(
    ! [A_156,A_159,B_157,E_158,B_160] :
      ( k1_partfun1(A_159,B_157,A_156,A_156,E_158,k2_funct_2(A_156,B_160)) = k5_relat_1(E_158,k2_funct_2(A_156,B_160))
      | ~ v1_funct_1(k2_funct_2(A_156,B_160))
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_157)))
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1(A_156,A_156)))
      | ~ v3_funct_2(B_160,A_156,A_156)
      | ~ v1_funct_2(B_160,A_156,A_156)
      | ~ v1_funct_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_30,c_481])).

tff(c_1715,plain,(
    ! [A_156,B_160] :
      ( k1_partfun1('#skF_1','#skF_1',A_156,A_156,'#skF_2',k2_funct_2(A_156,B_160)) = k5_relat_1('#skF_2',k2_funct_2(A_156,B_160))
      | ~ v1_funct_1(k2_funct_2(A_156,B_160))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1(A_156,A_156)))
      | ~ v3_funct_2(B_160,A_156,A_156)
      | ~ v1_funct_2(B_160,A_156,A_156)
      | ~ v1_funct_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_52,c_1699])).

tff(c_1740,plain,(
    ! [A_161,B_162] :
      ( k1_partfun1('#skF_1','#skF_1',A_161,A_161,'#skF_2',k2_funct_2(A_161,B_162)) = k5_relat_1('#skF_2',k2_funct_2(A_161,B_162))
      | ~ v1_funct_1(k2_funct_2(A_161,B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(A_161,A_161)))
      | ~ v3_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1715])).

tff(c_1756,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1740])).

tff(c_1776,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_340,c_339,c_339,c_339,c_1756])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_86,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_341,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_86])).

tff(c_1777,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_341])).

tff(c_1784,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1777])).

tff(c_1787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_268,c_214,c_293,c_1784])).

tff(c_1788,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2050,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2047,c_1788])).

tff(c_2569,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2050])).

tff(c_2576,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2569])).

tff(c_2579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_1944,c_1918,c_1900,c_2576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.97  
% 5.11/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.97  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.11/1.97  
% 5.11/1.97  %Foreground sorts:
% 5.11/1.97  
% 5.11/1.97  
% 5.11/1.97  %Background operators:
% 5.11/1.97  
% 5.11/1.97  
% 5.11/1.97  %Foreground operators:
% 5.11/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/1.97  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.11/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.11/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.11/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.11/1.97  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.11/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.11/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.11/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.11/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.11/1.97  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.11/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.11/1.97  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.11/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.11/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.11/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.11/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.11/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.11/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.11/1.97  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.11/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/1.97  
% 5.46/2.00  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.46/2.00  tff(f_145, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.46/2.00  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.46/2.00  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.46/2.00  tff(f_102, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.46/2.00  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.46/2.00  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.46/2.00  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.46/2.00  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.46/2.00  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.46/2.00  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.46/2.00  tff(f_98, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.46/2.00  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.46/2.00  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.46/2.00  tff(f_132, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.46/2.00  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.46/2.00  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.46/2.00  tff(c_73, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.00  tff(c_79, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_73])).
% 5.46/2.00  tff(c_85, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 5.46/2.00  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.46/2.00  tff(c_54, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.46/2.00  tff(c_1934, plain, (![C_201, A_202, B_203]: (v2_funct_1(C_201) | ~v3_funct_2(C_201, A_202, B_203) | ~v1_funct_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.46/2.00  tff(c_1940, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1934])).
% 5.46/2.00  tff(c_1944, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1940])).
% 5.46/2.00  tff(c_40, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.46/2.00  tff(c_1913, plain, (![A_194, B_195, D_196]: (r2_relset_1(A_194, B_195, D_196, D_196) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.46/2.00  tff(c_1918, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_40, c_1913])).
% 5.46/2.00  tff(c_1800, plain, (![C_167, B_168, A_169]: (v5_relat_1(C_167, B_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.46/2.00  tff(c_1808, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1800])).
% 5.46/2.00  tff(c_1812, plain, (![B_173, A_174]: (k2_relat_1(B_173)=A_174 | ~v2_funct_2(B_173, A_174) | ~v5_relat_1(B_173, A_174) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.46/2.00  tff(c_1818, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1808, c_1812])).
% 5.46/2.00  tff(c_1824, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1818])).
% 5.46/2.00  tff(c_1825, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1824])).
% 5.46/2.00  tff(c_1887, plain, (![C_190, B_191, A_192]: (v2_funct_2(C_190, B_191) | ~v3_funct_2(C_190, A_192, B_191) | ~v1_funct_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.46/2.00  tff(c_1893, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1887])).
% 5.46/2.00  tff(c_1897, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1893])).
% 5.46/2.00  tff(c_1899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1825, c_1897])).
% 5.46/2.00  tff(c_1900, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1824])).
% 5.46/2.00  tff(c_46, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.46/2.00  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.46/2.00  tff(c_60, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 5.46/2.00  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.46/2.00  tff(c_2037, plain, (![A_222, B_223]: (k2_funct_2(A_222, B_223)=k2_funct_1(B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.46/2.00  tff(c_2043, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2037])).
% 5.46/2.00  tff(c_2047, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2043])).
% 5.46/2.00  tff(c_2025, plain, (![A_219, B_220]: (v1_funct_1(k2_funct_2(A_219, B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.46/2.00  tff(c_2031, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2025])).
% 5.46/2.00  tff(c_2035, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2031])).
% 5.46/2.00  tff(c_2048, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2047, c_2035])).
% 5.46/2.00  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(k2_funct_2(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v3_funct_2(B_23, A_22, A_22) | ~v1_funct_2(B_23, A_22, A_22) | ~v1_funct_1(B_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.46/2.00  tff(c_2202, plain, (![F_235, A_233, C_234, D_232, B_236, E_237]: (k1_partfun1(A_233, B_236, C_234, D_232, E_237, F_235)=k5_relat_1(E_237, F_235) | ~m1_subset_1(F_235, k1_zfmisc_1(k2_zfmisc_1(C_234, D_232))) | ~v1_funct_1(F_235) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_236))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.46/2.00  tff(c_2210, plain, (![A_233, B_236, E_237]: (k1_partfun1(A_233, B_236, '#skF_1', '#skF_1', E_237, '#skF_2')=k5_relat_1(E_237, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_236))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_52, c_2202])).
% 5.46/2.00  tff(c_2239, plain, (![A_238, B_239, E_240]: (k1_partfun1(A_238, B_239, '#skF_1', '#skF_1', E_240, '#skF_2')=k5_relat_1(E_240, '#skF_2') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_1(E_240))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2210])).
% 5.46/2.00  tff(c_2490, plain, (![A_245, B_246]: (k1_partfun1(A_245, A_245, '#skF_1', '#skF_1', k2_funct_2(A_245, B_246), '#skF_2')=k5_relat_1(k2_funct_2(A_245, B_246), '#skF_2') | ~v1_funct_1(k2_funct_2(A_245, B_246)) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_zfmisc_1(A_245, A_245))) | ~v3_funct_2(B_246, A_245, A_245) | ~v1_funct_2(B_246, A_245, A_245) | ~v1_funct_1(B_246))), inference(resolution, [status(thm)], [c_30, c_2239])).
% 5.46/2.00  tff(c_2502, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2490])).
% 5.46/2.00  tff(c_2516, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2048, c_2047, c_2047, c_2047, c_2502])).
% 5.46/2.00  tff(c_258, plain, (![C_84, A_85, B_86]: (v2_funct_1(C_84) | ~v3_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.46/2.00  tff(c_264, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_258])).
% 5.46/2.00  tff(c_268, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_264])).
% 5.46/2.00  tff(c_209, plain, (![A_73, B_74, D_75]: (r2_relset_1(A_73, B_74, D_75, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.46/2.00  tff(c_214, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_40, c_209])).
% 5.46/2.00  tff(c_218, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.46/2.00  tff(c_226, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_218])).
% 5.46/2.00  tff(c_282, plain, (![A_92, B_93]: (k1_relset_1(A_92, A_92, B_93)=A_92 | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.46/2.00  tff(c_288, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_282])).
% 5.46/2.00  tff(c_293, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_226, c_288])).
% 5.46/2.00  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.46/2.00  tff(c_59, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 5.46/2.00  tff(c_329, plain, (![A_102, B_103]: (k2_funct_2(A_102, B_103)=k2_funct_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.46/2.00  tff(c_335, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_329])).
% 5.46/2.00  tff(c_339, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_335])).
% 5.46/2.00  tff(c_317, plain, (![A_99, B_100]: (v1_funct_1(k2_funct_2(A_99, B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.46/2.00  tff(c_323, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_317])).
% 5.46/2.00  tff(c_327, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_323])).
% 5.46/2.00  tff(c_340, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_327])).
% 5.46/2.00  tff(c_481, plain, (![C_115, F_116, D_113, E_118, A_114, B_117]: (k1_partfun1(A_114, B_117, C_115, D_113, E_118, F_116)=k5_relat_1(E_118, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_115, D_113))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_114, B_117))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.46/2.00  tff(c_1699, plain, (![A_156, A_159, B_157, E_158, B_160]: (k1_partfun1(A_159, B_157, A_156, A_156, E_158, k2_funct_2(A_156, B_160))=k5_relat_1(E_158, k2_funct_2(A_156, B_160)) | ~v1_funct_1(k2_funct_2(A_156, B_160)) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_157))) | ~v1_funct_1(E_158) | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1(A_156, A_156))) | ~v3_funct_2(B_160, A_156, A_156) | ~v1_funct_2(B_160, A_156, A_156) | ~v1_funct_1(B_160))), inference(resolution, [status(thm)], [c_30, c_481])).
% 5.46/2.00  tff(c_1715, plain, (![A_156, B_160]: (k1_partfun1('#skF_1', '#skF_1', A_156, A_156, '#skF_2', k2_funct_2(A_156, B_160))=k5_relat_1('#skF_2', k2_funct_2(A_156, B_160)) | ~v1_funct_1(k2_funct_2(A_156, B_160)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1(A_156, A_156))) | ~v3_funct_2(B_160, A_156, A_156) | ~v1_funct_2(B_160, A_156, A_156) | ~v1_funct_1(B_160))), inference(resolution, [status(thm)], [c_52, c_1699])).
% 5.46/2.00  tff(c_1740, plain, (![A_161, B_162]: (k1_partfun1('#skF_1', '#skF_1', A_161, A_161, '#skF_2', k2_funct_2(A_161, B_162))=k5_relat_1('#skF_2', k2_funct_2(A_161, B_162)) | ~v1_funct_1(k2_funct_2(A_161, B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1(A_161, A_161))) | ~v3_funct_2(B_162, A_161, A_161) | ~v1_funct_2(B_162, A_161, A_161) | ~v1_funct_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1715])).
% 5.46/2.00  tff(c_1756, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1740])).
% 5.46/2.00  tff(c_1776, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_340, c_339, c_339, c_339, c_1756])).
% 5.46/2.00  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.46/2.00  tff(c_86, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.46/2.00  tff(c_341, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_86])).
% 5.46/2.00  tff(c_1777, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_341])).
% 5.46/2.00  tff(c_1784, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_1777])).
% 5.46/2.00  tff(c_1787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_268, c_214, c_293, c_1784])).
% 5.46/2.00  tff(c_1788, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 5.46/2.00  tff(c_2050, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2047, c_1788])).
% 5.46/2.00  tff(c_2569, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2050])).
% 5.46/2.00  tff(c_2576, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60, c_2569])).
% 5.46/2.00  tff(c_2579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_1944, c_1918, c_1900, c_2576])).
% 5.46/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.00  
% 5.46/2.00  Inference rules
% 5.46/2.00  ----------------------
% 5.46/2.00  #Ref     : 0
% 5.46/2.00  #Sup     : 542
% 5.46/2.00  #Fact    : 0
% 5.46/2.00  #Define  : 0
% 5.46/2.00  #Split   : 4
% 5.46/2.00  #Chain   : 0
% 5.46/2.00  #Close   : 0
% 5.46/2.00  
% 5.46/2.00  Ordering : KBO
% 5.46/2.00  
% 5.46/2.00  Simplification rules
% 5.46/2.00  ----------------------
% 5.46/2.00  #Subsume      : 0
% 5.46/2.00  #Demod        : 1260
% 5.46/2.00  #Tautology    : 225
% 5.46/2.00  #SimpNegUnit  : 2
% 5.46/2.00  #BackRed      : 44
% 5.46/2.00  
% 5.46/2.00  #Partial instantiations: 0
% 5.46/2.00  #Strategies tried      : 1
% 5.46/2.00  
% 5.46/2.00  Timing (in seconds)
% 5.46/2.00  ----------------------
% 5.46/2.00  Preprocessing        : 0.36
% 5.46/2.00  Parsing              : 0.19
% 5.46/2.00  CNF conversion       : 0.02
% 5.46/2.00  Main loop            : 0.86
% 5.46/2.00  Inferencing          : 0.29
% 5.46/2.00  Reduction            : 0.33
% 5.46/2.00  Demodulation         : 0.24
% 5.46/2.00  BG Simplification    : 0.03
% 5.46/2.00  Subsumption          : 0.14
% 5.46/2.00  Abstraction          : 0.05
% 5.46/2.00  MUC search           : 0.00
% 5.46/2.00  Cooper               : 0.00
% 5.46/2.00  Total                : 1.26
% 5.46/2.00  Index Insertion      : 0.00
% 5.46/2.00  Index Deletion       : 0.00
% 5.46/2.00  Index Matching       : 0.00
% 5.46/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
