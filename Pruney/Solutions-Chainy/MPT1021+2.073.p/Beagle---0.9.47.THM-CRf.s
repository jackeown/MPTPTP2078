%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 498 expanded)
%              Number of leaves         :   40 ( 208 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 (1596 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_104,axiom,(
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

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_73,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1940,plain,(
    ! [C_184,A_185,B_186] :
      ( v2_funct_1(C_184)
      | ~ v3_funct_2(C_184,A_185,B_186)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1946,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1940])).

tff(c_1950,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1946])).

tff(c_42,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1914,plain,(
    ! [A_178,B_179,D_180] :
      ( r2_relset_1(A_178,B_179,D_180,D_180)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1919,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_42,c_1914])).

tff(c_1782,plain,(
    ! [C_152,B_153,A_154] :
      ( v5_relat_1(C_152,B_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1790,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1782])).

tff(c_1794,plain,(
    ! [B_158,A_159] :
      ( k2_relat_1(B_158) = A_159
      | ~ v2_funct_2(B_158,A_159)
      | ~ v5_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1800,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1790,c_1794])).

tff(c_1806,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1800])).

tff(c_1807,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1806])).

tff(c_1867,plain,(
    ! [C_172,B_173,A_174] :
      ( v2_funct_2(C_172,B_173)
      | ~ v3_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1873,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1867])).

tff(c_1877,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1873])).

tff(c_1879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1807,c_1877])).

tff(c_1880,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1806])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1993,plain,(
    ! [A_198,B_199] :
      ( k2_funct_2(A_198,B_199) = k2_funct_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1999,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1993])).

tff(c_2003,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1999])).

tff(c_1982,plain,(
    ! [A_196,B_197] :
      ( v1_funct_1(k2_funct_2(A_196,B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1988,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1982])).

tff(c_1992,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1988])).

tff(c_2004,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_1992])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2140,plain,(
    ! [C_211,D_215,A_216,B_214,F_212,E_213] :
      ( k1_partfun1(A_216,B_214,C_211,D_215,E_213,F_212) = k5_relat_1(E_213,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_211,D_215)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_1(E_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2148,plain,(
    ! [A_216,B_214,E_213] :
      ( k1_partfun1(A_216,B_214,'#skF_1','#skF_1',E_213,'#skF_2') = k5_relat_1(E_213,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_1(E_213) ) ),
    inference(resolution,[status(thm)],[c_52,c_2140])).

tff(c_2157,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_1','#skF_1',E_219,'#skF_2') = k5_relat_1(E_219,'#skF_2')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2148])).

tff(c_2428,plain,(
    ! [A_227,B_228] :
      ( k1_partfun1(A_227,A_227,'#skF_1','#skF_1',k2_funct_2(A_227,B_228),'#skF_2') = k5_relat_1(k2_funct_2(A_227,B_228),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k2_zfmisc_1(A_227,A_227)))
      | ~ v3_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_1(B_228) ) ),
    inference(resolution,[status(thm)],[c_32,c_2157])).

tff(c_2438,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2428])).

tff(c_2449,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2004,c_2003,c_2003,c_2003,c_2438])).

tff(c_244,plain,(
    ! [C_75,A_76,B_77] :
      ( v2_funct_1(C_75)
      | ~ v3_funct_2(C_75,A_76,B_77)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_250,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_244])).

tff(c_254,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_250])).

tff(c_198,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_203,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_42,c_198])).

tff(c_297,plain,(
    ! [A_91,B_92] :
      ( k2_funct_2(A_91,B_92) = k2_funct_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_303,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_297])).

tff(c_307,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_303])).

tff(c_281,plain,(
    ! [A_87,B_88] :
      ( v1_funct_1(k2_funct_2(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v3_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_287,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_281])).

tff(c_291,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_287])).

tff(c_308,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_291])).

tff(c_314,plain,(
    ! [A_93,B_94] :
      ( v3_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_318,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_314])).

tff(c_322,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_307,c_318])).

tff(c_334,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k2_funct_2(A_99,B_100),k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_364,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_334])).

tff(c_378,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_364])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( v2_funct_2(C_17,B_16)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_391,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_378,c_22])).

tff(c_420,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_322,c_391])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_405,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_378,c_2])).

tff(c_429,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_405])).

tff(c_14,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_425,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_378,c_14])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(B_19) = A_18
      | ~ v2_funct_2(B_19,A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_432,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_425,c_30])).

tff(c_435,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_432])).

tff(c_605,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_435])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_612,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_6])).

tff(c_624,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_254,c_612])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_447,plain,(
    ! [B_104,F_102,A_106,C_101,D_105,E_103] :
      ( k1_partfun1(A_106,B_104,C_101,D_105,E_103,F_102) = k5_relat_1(E_103,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_101,D_105)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_106,B_104)))
      | ~ v1_funct_1(E_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1674,plain,(
    ! [A_145,B_143,A_144,B_142,E_141] :
      ( k1_partfun1(A_145,B_143,A_144,A_144,E_141,k2_funct_2(A_144,B_142)) = k5_relat_1(E_141,k2_funct_2(A_144,B_142))
      | ~ v1_funct_1(k2_funct_2(A_144,B_142))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_145,B_143)))
      | ~ v1_funct_1(E_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v3_funct_2(B_142,A_144,A_144)
      | ~ v1_funct_2(B_142,A_144,A_144)
      | ~ v1_funct_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_32,c_447])).

tff(c_1692,plain,(
    ! [A_144,B_142] :
      ( k1_partfun1('#skF_1','#skF_1',A_144,A_144,'#skF_2',k2_funct_2(A_144,B_142)) = k5_relat_1('#skF_2',k2_funct_2(A_144,B_142))
      | ~ v1_funct_1(k2_funct_2(A_144,B_142))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v3_funct_2(B_142,A_144,A_144)
      | ~ v1_funct_2(B_142,A_144,A_144)
      | ~ v1_funct_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_52,c_1674])).

tff(c_1717,plain,(
    ! [A_146,B_147] :
      ( k1_partfun1('#skF_1','#skF_1',A_146,A_146,'#skF_2',k2_funct_2(A_146,B_147)) = k5_relat_1('#skF_2',k2_funct_2(A_146,B_147))
      | ~ v1_funct_1(k2_funct_2(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1692])).

tff(c_1735,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1717])).

tff(c_1758,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_308,c_307,c_307,c_307,c_1735])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_86,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_309,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_86])).

tff(c_1759,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_309])).

tff(c_1766,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1759])).

tff(c_1769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_254,c_203,c_624,c_1766])).

tff(c_1770,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2006,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_1770])).

tff(c_2471,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2449,c_2006])).

tff(c_2484,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2471])).

tff(c_2487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_1950,c_1919,c_1880,c_2484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.94  
% 5.08/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.94  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.08/1.94  
% 5.08/1.94  %Foreground sorts:
% 5.08/1.94  
% 5.08/1.94  
% 5.08/1.94  %Background operators:
% 5.08/1.94  
% 5.08/1.94  
% 5.08/1.94  %Foreground operators:
% 5.08/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.08/1.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.08/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.08/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.08/1.94  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.08/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.08/1.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.08/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.08/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.08/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.08/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.08/1.94  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.08/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.08/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.08/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.08/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.08/1.94  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.08/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.08/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.94  
% 5.08/1.97  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.08/1.97  tff(f_143, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.08/1.97  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.08/1.97  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.08/1.97  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.08/1.97  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.08/1.97  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.08/1.97  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.08/1.97  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.08/1.97  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.08/1.97  tff(f_128, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.08/1.97  tff(f_104, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.08/1.97  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.08/1.97  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.08/1.97  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.08/1.97  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.08/1.97  tff(c_73, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.08/1.97  tff(c_79, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_73])).
% 5.08/1.97  tff(c_85, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 5.08/1.97  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.08/1.97  tff(c_54, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.08/1.97  tff(c_1940, plain, (![C_184, A_185, B_186]: (v2_funct_1(C_184) | ~v3_funct_2(C_184, A_185, B_186) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.08/1.97  tff(c_1946, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1940])).
% 5.08/1.97  tff(c_1950, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1946])).
% 5.08/1.97  tff(c_42, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.08/1.97  tff(c_1914, plain, (![A_178, B_179, D_180]: (r2_relset_1(A_178, B_179, D_180, D_180) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.08/1.97  tff(c_1919, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_42, c_1914])).
% 5.08/1.97  tff(c_1782, plain, (![C_152, B_153, A_154]: (v5_relat_1(C_152, B_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.08/1.97  tff(c_1790, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1782])).
% 5.08/1.97  tff(c_1794, plain, (![B_158, A_159]: (k2_relat_1(B_158)=A_159 | ~v2_funct_2(B_158, A_159) | ~v5_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.08/1.97  tff(c_1800, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1790, c_1794])).
% 5.08/1.97  tff(c_1806, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1800])).
% 5.08/1.97  tff(c_1807, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1806])).
% 5.08/1.97  tff(c_1867, plain, (![C_172, B_173, A_174]: (v2_funct_2(C_172, B_173) | ~v3_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.08/1.97  tff(c_1873, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1867])).
% 5.08/1.97  tff(c_1877, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1873])).
% 5.08/1.97  tff(c_1879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1807, c_1877])).
% 5.08/1.97  tff(c_1880, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1806])).
% 5.08/1.97  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.08/1.97  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.08/1.97  tff(c_60, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 5.08/1.97  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.08/1.97  tff(c_1993, plain, (![A_198, B_199]: (k2_funct_2(A_198, B_199)=k2_funct_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.08/1.97  tff(c_1999, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1993])).
% 5.08/1.97  tff(c_2003, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1999])).
% 5.08/1.97  tff(c_1982, plain, (![A_196, B_197]: (v1_funct_1(k2_funct_2(A_196, B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_1988, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1982])).
% 5.08/1.97  tff(c_1992, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1988])).
% 5.08/1.97  tff(c_2004, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_1992])).
% 5.08/1.97  tff(c_32, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_2140, plain, (![C_211, D_215, A_216, B_214, F_212, E_213]: (k1_partfun1(A_216, B_214, C_211, D_215, E_213, F_212)=k5_relat_1(E_213, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_211, D_215))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_1(E_213))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.08/1.97  tff(c_2148, plain, (![A_216, B_214, E_213]: (k1_partfun1(A_216, B_214, '#skF_1', '#skF_1', E_213, '#skF_2')=k5_relat_1(E_213, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_1(E_213))), inference(resolution, [status(thm)], [c_52, c_2140])).
% 5.08/1.97  tff(c_2157, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_1', '#skF_1', E_219, '#skF_2')=k5_relat_1(E_219, '#skF_2') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2148])).
% 5.08/1.97  tff(c_2428, plain, (![A_227, B_228]: (k1_partfun1(A_227, A_227, '#skF_1', '#skF_1', k2_funct_2(A_227, B_228), '#skF_2')=k5_relat_1(k2_funct_2(A_227, B_228), '#skF_2') | ~v1_funct_1(k2_funct_2(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(k2_zfmisc_1(A_227, A_227))) | ~v3_funct_2(B_228, A_227, A_227) | ~v1_funct_2(B_228, A_227, A_227) | ~v1_funct_1(B_228))), inference(resolution, [status(thm)], [c_32, c_2157])).
% 5.08/1.97  tff(c_2438, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2428])).
% 5.08/1.97  tff(c_2449, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2004, c_2003, c_2003, c_2003, c_2438])).
% 5.08/1.97  tff(c_244, plain, (![C_75, A_76, B_77]: (v2_funct_1(C_75) | ~v3_funct_2(C_75, A_76, B_77) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.08/1.97  tff(c_250, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_244])).
% 5.08/1.97  tff(c_254, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_250])).
% 5.08/1.97  tff(c_198, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.08/1.97  tff(c_203, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_42, c_198])).
% 5.08/1.97  tff(c_297, plain, (![A_91, B_92]: (k2_funct_2(A_91, B_92)=k2_funct_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.08/1.97  tff(c_303, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_297])).
% 5.08/1.97  tff(c_307, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_303])).
% 5.08/1.97  tff(c_281, plain, (![A_87, B_88]: (v1_funct_1(k2_funct_2(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v3_funct_2(B_88, A_87, A_87) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_287, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_281])).
% 5.08/1.97  tff(c_291, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_287])).
% 5.08/1.97  tff(c_308, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_291])).
% 5.08/1.97  tff(c_314, plain, (![A_93, B_94]: (v3_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_318, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_314])).
% 5.08/1.97  tff(c_322, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_307, c_318])).
% 5.08/1.97  tff(c_334, plain, (![A_99, B_100]: (m1_subset_1(k2_funct_2(A_99, B_100), k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_364, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_307, c_334])).
% 5.08/1.97  tff(c_378, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_364])).
% 5.08/1.97  tff(c_22, plain, (![C_17, B_16, A_15]: (v2_funct_2(C_17, B_16) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.08/1.97  tff(c_391, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_378, c_22])).
% 5.08/1.97  tff(c_420, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_322, c_391])).
% 5.08/1.97  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.08/1.97  tff(c_405, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_378, c_2])).
% 5.08/1.97  tff(c_429, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_405])).
% 5.08/1.97  tff(c_14, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.08/1.97  tff(c_425, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_378, c_14])).
% 5.08/1.97  tff(c_30, plain, (![B_19, A_18]: (k2_relat_1(B_19)=A_18 | ~v2_funct_2(B_19, A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.08/1.97  tff(c_432, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_425, c_30])).
% 5.08/1.97  tff(c_435, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_432])).
% 5.08/1.97  tff(c_605, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_435])).
% 5.08/1.97  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.08/1.97  tff(c_612, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_605, c_6])).
% 5.08/1.97  tff(c_624, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_254, c_612])).
% 5.08/1.97  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.08/1.97  tff(c_59, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 5.08/1.97  tff(c_447, plain, (![B_104, F_102, A_106, C_101, D_105, E_103]: (k1_partfun1(A_106, B_104, C_101, D_105, E_103, F_102)=k5_relat_1(E_103, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_101, D_105))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_106, B_104))) | ~v1_funct_1(E_103))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.08/1.97  tff(c_1674, plain, (![A_145, B_143, A_144, B_142, E_141]: (k1_partfun1(A_145, B_143, A_144, A_144, E_141, k2_funct_2(A_144, B_142))=k5_relat_1(E_141, k2_funct_2(A_144, B_142)) | ~v1_funct_1(k2_funct_2(A_144, B_142)) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_145, B_143))) | ~v1_funct_1(E_141) | ~m1_subset_1(B_142, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v3_funct_2(B_142, A_144, A_144) | ~v1_funct_2(B_142, A_144, A_144) | ~v1_funct_1(B_142))), inference(resolution, [status(thm)], [c_32, c_447])).
% 5.08/1.97  tff(c_1692, plain, (![A_144, B_142]: (k1_partfun1('#skF_1', '#skF_1', A_144, A_144, '#skF_2', k2_funct_2(A_144, B_142))=k5_relat_1('#skF_2', k2_funct_2(A_144, B_142)) | ~v1_funct_1(k2_funct_2(A_144, B_142)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v3_funct_2(B_142, A_144, A_144) | ~v1_funct_2(B_142, A_144, A_144) | ~v1_funct_1(B_142))), inference(resolution, [status(thm)], [c_52, c_1674])).
% 5.08/1.97  tff(c_1717, plain, (![A_146, B_147]: (k1_partfun1('#skF_1', '#skF_1', A_146, A_146, '#skF_2', k2_funct_2(A_146, B_147))=k5_relat_1('#skF_2', k2_funct_2(A_146, B_147)) | ~v1_funct_1(k2_funct_2(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_147, A_146, A_146) | ~v1_funct_2(B_147, A_146, A_146) | ~v1_funct_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1692])).
% 5.08/1.97  tff(c_1735, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1717])).
% 5.08/1.97  tff(c_1758, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_308, c_307, c_307, c_307, c_1735])).
% 5.08/1.97  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.08/1.97  tff(c_86, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.08/1.97  tff(c_309, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_86])).
% 5.08/1.97  tff(c_1759, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_309])).
% 5.08/1.97  tff(c_1766, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_1759])).
% 5.08/1.97  tff(c_1769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_254, c_203, c_624, c_1766])).
% 5.08/1.97  tff(c_1770, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 5.08/1.97  tff(c_2006, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_1770])).
% 5.08/1.97  tff(c_2471, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2449, c_2006])).
% 5.08/1.97  tff(c_2484, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60, c_2471])).
% 5.08/1.97  tff(c_2487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_1950, c_1919, c_1880, c_2484])).
% 5.08/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.97  
% 5.08/1.97  Inference rules
% 5.08/1.97  ----------------------
% 5.08/1.97  #Ref     : 0
% 5.08/1.97  #Sup     : 504
% 5.08/1.97  #Fact    : 0
% 5.08/1.97  #Define  : 0
% 5.08/1.97  #Split   : 4
% 5.08/1.97  #Chain   : 0
% 5.08/1.97  #Close   : 0
% 5.08/1.97  
% 5.08/1.97  Ordering : KBO
% 5.08/1.97  
% 5.08/1.97  Simplification rules
% 5.08/1.97  ----------------------
% 5.08/1.97  #Subsume      : 1
% 5.08/1.97  #Demod        : 1288
% 5.08/1.97  #Tautology    : 212
% 5.08/1.97  #SimpNegUnit  : 2
% 5.08/1.97  #BackRed      : 42
% 5.08/1.97  
% 5.08/1.97  #Partial instantiations: 0
% 5.08/1.97  #Strategies tried      : 1
% 5.08/1.97  
% 5.08/1.97  Timing (in seconds)
% 5.08/1.97  ----------------------
% 5.08/1.97  Preprocessing        : 0.35
% 5.08/1.97  Parsing              : 0.19
% 5.08/1.97  CNF conversion       : 0.02
% 5.08/1.97  Main loop            : 0.82
% 5.08/1.97  Inferencing          : 0.28
% 5.08/1.97  Reduction            : 0.31
% 5.08/1.97  Demodulation         : 0.24
% 5.08/1.97  BG Simplification    : 0.03
% 5.08/1.97  Subsumption          : 0.14
% 5.08/1.97  Abstraction          : 0.04
% 5.08/1.97  MUC search           : 0.00
% 5.08/1.97  Cooper               : 0.00
% 5.08/1.97  Total                : 1.23
% 5.08/1.97  Index Insertion      : 0.00
% 5.08/1.97  Index Deletion       : 0.00
% 5.08/1.97  Index Matching       : 0.00
% 5.08/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
