%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 480 expanded)
%              Number of leaves         :   39 ( 202 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 (1560 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_99,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1938,plain,(
    ! [C_182,A_183,B_184] :
      ( v2_funct_1(C_182)
      | ~ v3_funct_2(C_182,A_183,B_184)
      | ~ v1_funct_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1944,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1938])).

tff(c_1948,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1944])).

tff(c_40,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1912,plain,(
    ! [A_176,B_177,D_178] :
      ( r2_relset_1(A_176,B_177,D_178,D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1917,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_40,c_1912])).

tff(c_1771,plain,(
    ! [C_147,B_148,A_149] :
      ( v5_relat_1(C_147,B_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1779,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1771])).

tff(c_1792,plain,(
    ! [B_156,A_157] :
      ( k2_relat_1(B_156) = A_157
      | ~ v2_funct_2(B_156,A_157)
      | ~ v5_relat_1(B_156,A_157)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1798,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1779,c_1792])).

tff(c_1804,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1798])).

tff(c_1805,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1804])).

tff(c_1865,plain,(
    ! [C_170,B_171,A_172] :
      ( v2_funct_2(C_170,B_171)
      | ~ v3_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1871,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1865])).

tff(c_1875,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1871])).

tff(c_1877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1805,c_1875])).

tff(c_1878,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1804])).

tff(c_46,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1991,plain,(
    ! [A_196,B_197] :
      ( k2_funct_2(A_196,B_197) = k2_funct_1(B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1997,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1991])).

tff(c_2001,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1997])).

tff(c_1980,plain,(
    ! [A_194,B_195] :
      ( v1_funct_1(k2_funct_2(A_194,B_195))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1986,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1980])).

tff(c_1990,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1986])).

tff(c_2002,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2001,c_1990])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_funct_2(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2134,plain,(
    ! [C_211,A_209,D_210,F_212,B_213,E_214] :
      ( k1_partfun1(A_209,B_213,C_211,D_210,E_214,F_212) = k5_relat_1(E_214,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_211,D_210)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_209,B_213)))
      | ~ v1_funct_1(E_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2142,plain,(
    ! [A_209,B_213,E_214] :
      ( k1_partfun1(A_209,B_213,'#skF_1','#skF_1',E_214,'#skF_2') = k5_relat_1(E_214,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_209,B_213)))
      | ~ v1_funct_1(E_214) ) ),
    inference(resolution,[status(thm)],[c_50,c_2134])).

tff(c_2157,plain,(
    ! [A_215,B_216,E_217] :
      ( k1_partfun1(A_215,B_216,'#skF_1','#skF_1',E_217,'#skF_2') = k5_relat_1(E_217,'#skF_2')
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(E_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2142])).

tff(c_2421,plain,(
    ! [A_225,B_226] :
      ( k1_partfun1(A_225,A_225,'#skF_1','#skF_1',k2_funct_2(A_225,B_226),'#skF_2') = k5_relat_1(k2_funct_2(A_225,B_226),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_225,B_226))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(resolution,[status(thm)],[c_30,c_2157])).

tff(c_2431,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2421])).

tff(c_2442,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2002,c_2001,c_2001,c_2001,c_2431])).

tff(c_249,plain,(
    ! [C_73,A_74,B_75] :
      ( v2_funct_1(C_73)
      | ~ v3_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_255,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_249])).

tff(c_259,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_255])).

tff(c_223,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_40,c_223])).

tff(c_302,plain,(
    ! [A_89,B_90] :
      ( k2_funct_2(A_89,B_90) = k2_funct_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_308,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_302])).

tff(c_312,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_308])).

tff(c_286,plain,(
    ! [A_85,B_86] :
      ( v1_funct_1(k2_funct_2(A_85,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_292,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_286])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_292])).

tff(c_313,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_296])).

tff(c_319,plain,(
    ! [A_91,B_92] :
      ( v3_funct_2(k2_funct_2(A_91,B_92),A_91,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_323,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_319])).

tff(c_327,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_312,c_323])).

tff(c_339,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_funct_2(A_97,B_98),k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_369,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_339])).

tff(c_381,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_369])).

tff(c_20,plain,(
    ! [C_15,B_14,A_13] :
      ( v2_funct_2(C_15,B_14)
      | ~ v3_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_394,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_381,c_20])).

tff(c_423,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_327,c_394])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_430,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_381,c_10])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( v5_relat_1(C_8,B_7)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_429,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_381,c_12])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(B_17) = A_16
      | ~ v2_funct_2(B_17,A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_433,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_429,c_28])).

tff(c_436,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_433])).

tff(c_604,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_436])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_611,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_2])).

tff(c_623,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_259,c_611])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_448,plain,(
    ! [E_104,F_102,B_103,A_99,D_100,C_101] :
      ( k1_partfun1(A_99,B_103,C_101,D_100,E_104,F_102) = k5_relat_1(E_104,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_101,D_100)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_99,B_103)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1669,plain,(
    ! [B_143,A_139,E_142,B_141,A_140] :
      ( k1_partfun1(A_139,B_141,A_140,A_140,E_142,k2_funct_2(A_140,B_143)) = k5_relat_1(E_142,k2_funct_2(A_140,B_143))
      | ~ v1_funct_1(k2_funct_2(A_140,B_143))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_139,B_141)))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_140,A_140)))
      | ~ v3_funct_2(B_143,A_140,A_140)
      | ~ v1_funct_2(B_143,A_140,A_140)
      | ~ v1_funct_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_30,c_448])).

tff(c_1687,plain,(
    ! [A_140,B_143] :
      ( k1_partfun1('#skF_1','#skF_1',A_140,A_140,'#skF_2',k2_funct_2(A_140,B_143)) = k5_relat_1('#skF_2',k2_funct_2(A_140,B_143))
      | ~ v1_funct_1(k2_funct_2(A_140,B_143))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_140,A_140)))
      | ~ v3_funct_2(B_143,A_140,A_140)
      | ~ v1_funct_2(B_143,A_140,A_140)
      | ~ v1_funct_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_50,c_1669])).

tff(c_1715,plain,(
    ! [A_144,B_145] :
      ( k1_partfun1('#skF_1','#skF_1',A_144,A_144,'#skF_2',k2_funct_2(A_144,B_145)) = k5_relat_1('#skF_2',k2_funct_2(A_144,B_145))
      | ~ v1_funct_1(k2_funct_2(A_144,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v3_funct_2(B_145,A_144,A_144)
      | ~ v1_funct_2(B_145,A_144,A_144)
      | ~ v1_funct_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1687])).

tff(c_1733,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1715])).

tff(c_1756,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_313,c_312,c_312,c_312,c_1733])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_314,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_79])).

tff(c_1757,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_314])).

tff(c_1764,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1757])).

tff(c_1767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_259,c_228,c_623,c_1764])).

tff(c_1768,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2004,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2001,c_1768])).

tff(c_2470,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_2004])).

tff(c_2477,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2470])).

tff(c_2480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_1948,c_1917,c_1878,c_2477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.97  
% 4.89/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.97  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.89/1.97  
% 4.89/1.97  %Foreground sorts:
% 4.89/1.97  
% 4.89/1.97  
% 4.89/1.97  %Background operators:
% 4.89/1.97  
% 4.89/1.97  
% 4.89/1.97  %Foreground operators:
% 4.89/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.89/1.97  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.89/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.89/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.89/1.97  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.89/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.89/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.89/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.97  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.89/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.97  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.89/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.89/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.89/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.89/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.89/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.89/1.97  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.89/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.89/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.89/1.97  
% 4.89/1.99  tff(f_138, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 4.89/1.99  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.89/1.99  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.89/1.99  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.89/1.99  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.89/1.99  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.89/1.99  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.89/1.99  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.89/1.99  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.89/1.99  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.89/1.99  tff(f_99, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.89/1.99  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.89/1.99  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.89/1.99  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.89/1.99  tff(c_70, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.99  tff(c_78, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_70])).
% 4.89/1.99  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.89/1.99  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.89/1.99  tff(c_1938, plain, (![C_182, A_183, B_184]: (v2_funct_1(C_182) | ~v3_funct_2(C_182, A_183, B_184) | ~v1_funct_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.99  tff(c_1944, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1938])).
% 4.89/1.99  tff(c_1948, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1944])).
% 4.89/1.99  tff(c_40, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.89/1.99  tff(c_1912, plain, (![A_176, B_177, D_178]: (r2_relset_1(A_176, B_177, D_178, D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.89/1.99  tff(c_1917, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_40, c_1912])).
% 4.89/1.99  tff(c_1771, plain, (![C_147, B_148, A_149]: (v5_relat_1(C_147, B_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.99  tff(c_1779, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1771])).
% 4.89/1.99  tff(c_1792, plain, (![B_156, A_157]: (k2_relat_1(B_156)=A_157 | ~v2_funct_2(B_156, A_157) | ~v5_relat_1(B_156, A_157) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.99  tff(c_1798, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1779, c_1792])).
% 4.89/1.99  tff(c_1804, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1798])).
% 4.89/1.99  tff(c_1805, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1804])).
% 4.89/1.99  tff(c_1865, plain, (![C_170, B_171, A_172]: (v2_funct_2(C_170, B_171) | ~v3_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.99  tff(c_1871, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1865])).
% 4.89/1.99  tff(c_1875, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1871])).
% 4.89/1.99  tff(c_1877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1805, c_1875])).
% 4.89/1.99  tff(c_1878, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1804])).
% 4.89/1.99  tff(c_46, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.89/1.99  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.89/1.99  tff(c_58, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 4.89/1.99  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.89/1.99  tff(c_1991, plain, (![A_196, B_197]: (k2_funct_2(A_196, B_197)=k2_funct_1(B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.89/1.99  tff(c_1997, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1991])).
% 4.89/1.99  tff(c_2001, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1997])).
% 4.89/1.99  tff(c_1980, plain, (![A_194, B_195]: (v1_funct_1(k2_funct_2(A_194, B_195)) | ~m1_subset_1(B_195, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_195, A_194, A_194) | ~v1_funct_2(B_195, A_194, A_194) | ~v1_funct_1(B_195))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.89/1.99  tff(c_1986, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1980])).
% 4.89/1.99  tff(c_1990, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1986])).
% 4.89/1.99  tff(c_2002, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2001, c_1990])).
% 4.89/1.99  tff(c_30, plain, (![A_18, B_19]: (m1_subset_1(k2_funct_2(A_18, B_19), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.89/1.99  tff(c_2134, plain, (![C_211, A_209, D_210, F_212, B_213, E_214]: (k1_partfun1(A_209, B_213, C_211, D_210, E_214, F_212)=k5_relat_1(E_214, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_211, D_210))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_209, B_213))) | ~v1_funct_1(E_214))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.99  tff(c_2142, plain, (![A_209, B_213, E_214]: (k1_partfun1(A_209, B_213, '#skF_1', '#skF_1', E_214, '#skF_2')=k5_relat_1(E_214, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_209, B_213))) | ~v1_funct_1(E_214))), inference(resolution, [status(thm)], [c_50, c_2134])).
% 4.89/1.99  tff(c_2157, plain, (![A_215, B_216, E_217]: (k1_partfun1(A_215, B_216, '#skF_1', '#skF_1', E_217, '#skF_2')=k5_relat_1(E_217, '#skF_2') | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(E_217))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2142])).
% 4.89/1.99  tff(c_2421, plain, (![A_225, B_226]: (k1_partfun1(A_225, A_225, '#skF_1', '#skF_1', k2_funct_2(A_225, B_226), '#skF_2')=k5_relat_1(k2_funct_2(A_225, B_226), '#skF_2') | ~v1_funct_1(k2_funct_2(A_225, B_226)) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(resolution, [status(thm)], [c_30, c_2157])).
% 4.89/1.99  tff(c_2431, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2421])).
% 4.89/1.99  tff(c_2442, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2002, c_2001, c_2001, c_2001, c_2431])).
% 4.89/1.99  tff(c_249, plain, (![C_73, A_74, B_75]: (v2_funct_1(C_73) | ~v3_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.99  tff(c_255, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_249])).
% 4.89/1.99  tff(c_259, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_255])).
% 4.89/1.99  tff(c_223, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.89/1.99  tff(c_228, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_40, c_223])).
% 4.89/1.99  tff(c_302, plain, (![A_89, B_90]: (k2_funct_2(A_89, B_90)=k2_funct_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.89/1.99  tff(c_308, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_302])).
% 4.89/1.99  tff(c_312, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_308])).
% 4.89/1.99  tff(c_286, plain, (![A_85, B_86]: (v1_funct_1(k2_funct_2(A_85, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.89/1.99  tff(c_292, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_286])).
% 4.89/1.99  tff(c_296, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_292])).
% 4.89/1.99  tff(c_313, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_296])).
% 4.89/1.99  tff(c_319, plain, (![A_91, B_92]: (v3_funct_2(k2_funct_2(A_91, B_92), A_91, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.89/1.99  tff(c_323, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_319])).
% 4.89/1.99  tff(c_327, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_312, c_323])).
% 4.89/1.99  tff(c_339, plain, (![A_97, B_98]: (m1_subset_1(k2_funct_2(A_97, B_98), k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.89/1.99  tff(c_369, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_312, c_339])).
% 4.89/1.99  tff(c_381, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_369])).
% 4.89/1.99  tff(c_20, plain, (![C_15, B_14, A_13]: (v2_funct_2(C_15, B_14) | ~v3_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.99  tff(c_394, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_381, c_20])).
% 4.89/1.99  tff(c_423, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_327, c_394])).
% 4.89/1.99  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.99  tff(c_430, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_381, c_10])).
% 4.89/1.99  tff(c_12, plain, (![C_8, B_7, A_6]: (v5_relat_1(C_8, B_7) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.99  tff(c_429, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_381, c_12])).
% 4.89/1.99  tff(c_28, plain, (![B_17, A_16]: (k2_relat_1(B_17)=A_16 | ~v2_funct_2(B_17, A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.99  tff(c_433, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_429, c_28])).
% 4.89/1.99  tff(c_436, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_433])).
% 4.89/1.99  tff(c_604, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_436])).
% 4.89/1.99  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.89/1.99  tff(c_611, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_604, c_2])).
% 4.89/1.99  tff(c_623, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_259, c_611])).
% 4.89/1.99  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.89/1.99  tff(c_57, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 4.89/1.99  tff(c_448, plain, (![E_104, F_102, B_103, A_99, D_100, C_101]: (k1_partfun1(A_99, B_103, C_101, D_100, E_104, F_102)=k5_relat_1(E_104, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_101, D_100))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_99, B_103))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.99  tff(c_1669, plain, (![B_143, A_139, E_142, B_141, A_140]: (k1_partfun1(A_139, B_141, A_140, A_140, E_142, k2_funct_2(A_140, B_143))=k5_relat_1(E_142, k2_funct_2(A_140, B_143)) | ~v1_funct_1(k2_funct_2(A_140, B_143)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_139, B_141))) | ~v1_funct_1(E_142) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_140, A_140))) | ~v3_funct_2(B_143, A_140, A_140) | ~v1_funct_2(B_143, A_140, A_140) | ~v1_funct_1(B_143))), inference(resolution, [status(thm)], [c_30, c_448])).
% 4.89/1.99  tff(c_1687, plain, (![A_140, B_143]: (k1_partfun1('#skF_1', '#skF_1', A_140, A_140, '#skF_2', k2_funct_2(A_140, B_143))=k5_relat_1('#skF_2', k2_funct_2(A_140, B_143)) | ~v1_funct_1(k2_funct_2(A_140, B_143)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_140, A_140))) | ~v3_funct_2(B_143, A_140, A_140) | ~v1_funct_2(B_143, A_140, A_140) | ~v1_funct_1(B_143))), inference(resolution, [status(thm)], [c_50, c_1669])).
% 4.89/1.99  tff(c_1715, plain, (![A_144, B_145]: (k1_partfun1('#skF_1', '#skF_1', A_144, A_144, '#skF_2', k2_funct_2(A_144, B_145))=k5_relat_1('#skF_2', k2_funct_2(A_144, B_145)) | ~v1_funct_1(k2_funct_2(A_144, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v3_funct_2(B_145, A_144, A_144) | ~v1_funct_2(B_145, A_144, A_144) | ~v1_funct_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1687])).
% 4.89/1.99  tff(c_1733, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1715])).
% 4.89/1.99  tff(c_1756, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_313, c_312, c_312, c_312, c_1733])).
% 4.89/1.99  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.89/1.99  tff(c_79, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.89/1.99  tff(c_314, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_79])).
% 4.89/1.99  tff(c_1757, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_314])).
% 4.89/1.99  tff(c_1764, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1757])).
% 4.89/1.99  tff(c_1767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_259, c_228, c_623, c_1764])).
% 4.89/1.99  tff(c_1768, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 4.89/1.99  tff(c_2004, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2001, c_1768])).
% 4.89/1.99  tff(c_2470, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_2004])).
% 4.89/1.99  tff(c_2477, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2470])).
% 4.89/1.99  tff(c_2480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_1948, c_1917, c_1878, c_2477])).
% 4.89/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.99  
% 4.89/1.99  Inference rules
% 4.89/1.99  ----------------------
% 4.89/1.99  #Ref     : 0
% 4.89/1.99  #Sup     : 507
% 4.89/1.99  #Fact    : 0
% 4.89/1.99  #Define  : 0
% 4.89/1.99  #Split   : 4
% 4.89/1.99  #Chain   : 0
% 4.89/1.99  #Close   : 0
% 4.89/1.99  
% 4.89/1.99  Ordering : KBO
% 4.89/1.99  
% 4.89/1.99  Simplification rules
% 4.89/1.99  ----------------------
% 4.89/1.99  #Subsume      : 1
% 4.89/1.99  #Demod        : 1281
% 4.89/1.99  #Tautology    : 215
% 4.89/1.99  #SimpNegUnit  : 2
% 4.89/2.00  #BackRed      : 42
% 4.89/2.00  
% 4.89/2.00  #Partial instantiations: 0
% 4.89/2.00  #Strategies tried      : 1
% 5.28/2.00  
% 5.28/2.00  Timing (in seconds)
% 5.28/2.00  ----------------------
% 5.28/2.00  Preprocessing        : 0.35
% 5.28/2.00  Parsing              : 0.19
% 5.28/2.00  CNF conversion       : 0.02
% 5.28/2.00  Main loop            : 0.79
% 5.28/2.00  Inferencing          : 0.27
% 5.28/2.00  Reduction            : 0.30
% 5.28/2.00  Demodulation         : 0.23
% 5.28/2.00  BG Simplification    : 0.03
% 5.28/2.00  Subsumption          : 0.13
% 5.28/2.00  Abstraction          : 0.03
% 5.28/2.00  MUC search           : 0.00
% 5.28/2.00  Cooper               : 0.00
% 5.28/2.00  Total                : 1.20
% 5.28/2.00  Index Insertion      : 0.00
% 5.28/2.00  Index Deletion       : 0.00
% 5.28/2.00  Index Matching       : 0.00
% 5.28/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
