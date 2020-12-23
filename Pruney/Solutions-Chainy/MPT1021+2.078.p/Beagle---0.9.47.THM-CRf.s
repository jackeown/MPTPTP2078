%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 503 expanded)
%              Number of leaves         :   39 ( 209 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 (1600 expanded)
%              Number of equality atoms :   43 ( 111 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_141,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_106,axiom,(
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

tff(f_116,axiom,(
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

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_71,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1951,plain,(
    ! [C_184,A_185,B_186] :
      ( v2_funct_1(C_184)
      | ~ v3_funct_2(C_184,A_185,B_186)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1957,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1951])).

tff(c_1961,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1957])).

tff(c_46,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_1913,plain,(
    ! [A_177,B_178,D_179] :
      ( r2_relset_1(A_177,B_178,D_179,D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1918,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_57,c_1913])).

tff(c_1784,plain,(
    ! [C_149,B_150,A_151] :
      ( v5_relat_1(C_149,B_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1792,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1784])).

tff(c_1805,plain,(
    ! [B_158,A_159] :
      ( k2_relat_1(B_158) = A_159
      | ~ v2_funct_2(B_158,A_159)
      | ~ v5_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1811,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1792,c_1805])).

tff(c_1817,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1811])).

tff(c_1818,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1878,plain,(
    ! [C_172,B_173,A_174] :
      ( v2_funct_2(C_172,B_173)
      | ~ v3_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1884,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1878])).

tff(c_1888,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1884])).

tff(c_1890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_1888])).

tff(c_1891,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2004,plain,(
    ! [A_198,B_199] :
      ( k2_funct_2(A_198,B_199) = k2_funct_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2010,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2004])).

tff(c_2014,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2010])).

tff(c_1993,plain,(
    ! [A_196,B_197] :
      ( v1_funct_1(k2_funct_2(A_196,B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1999,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1993])).

tff(c_2003,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1999])).

tff(c_2015,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2014,c_2003])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2151,plain,(
    ! [C_211,D_215,A_216,B_214,F_212,E_213] :
      ( k1_partfun1(A_216,B_214,C_211,D_215,E_213,F_212) = k5_relat_1(E_213,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_211,D_215)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_1(E_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2159,plain,(
    ! [A_216,B_214,E_213] :
      ( k1_partfun1(A_216,B_214,'#skF_1','#skF_1',E_213,'#skF_2') = k5_relat_1(E_213,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_1(E_213) ) ),
    inference(resolution,[status(thm)],[c_50,c_2151])).

tff(c_2174,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_1','#skF_1',E_219,'#skF_2') = k5_relat_1(E_219,'#skF_2')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2159])).

tff(c_2439,plain,(
    ! [A_227,B_228] :
      ( k1_partfun1(A_227,A_227,'#skF_1','#skF_1',k2_funct_2(A_227,B_228),'#skF_2') = k5_relat_1(k2_funct_2(A_227,B_228),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k2_zfmisc_1(A_227,A_227)))
      | ~ v3_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_1(B_228) ) ),
    inference(resolution,[status(thm)],[c_34,c_2174])).

tff(c_2449,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2439])).

tff(c_2460,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2015,c_2014,c_2014,c_2014,c_2449])).

tff(c_254,plain,(
    ! [C_75,A_76,B_77] :
      ( v2_funct_1(C_75)
      | ~ v3_funct_2(C_75,A_76,B_77)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_260,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_254])).

tff(c_264,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_260])).

tff(c_205,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_210,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_57,c_205])).

tff(c_307,plain,(
    ! [A_91,B_92] :
      ( k2_funct_2(A_91,B_92) = k2_funct_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_313,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_307])).

tff(c_317,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_313])).

tff(c_291,plain,(
    ! [A_87,B_88] :
      ( v1_funct_1(k2_funct_2(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v3_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_297,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_291])).

tff(c_301,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_297])).

tff(c_318,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_301])).

tff(c_335,plain,(
    ! [A_97,B_98] :
      ( v3_funct_2(k2_funct_2(A_97,B_98),A_97,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_339,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_335])).

tff(c_343,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_317,c_339])).

tff(c_344,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k2_funct_2(A_99,B_100),k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_374,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_344])).

tff(c_388,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_374])).

tff(c_24,plain,(
    ! [C_18,B_17,A_16] :
      ( v2_funct_2(C_18,B_17)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_401,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_388,c_24])).

tff(c_430,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_343,c_401])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_415,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_439,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_415])).

tff(c_14,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_436,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_388,c_14])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(B_20) = A_19
      | ~ v2_funct_2(B_20,A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_442,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_436,c_32])).

tff(c_445,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_442])).

tff(c_615,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_445])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_622,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_6])).

tff(c_634,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_264,c_622])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_457,plain,(
    ! [B_104,F_102,A_106,C_101,D_105,E_103] :
      ( k1_partfun1(A_106,B_104,C_101,D_105,E_103,F_102) = k5_relat_1(E_103,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_101,D_105)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_106,B_104)))
      | ~ v1_funct_1(E_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1685,plain,(
    ! [B_144,A_141,A_145,B_143,E_142] :
      ( k1_partfun1(A_145,B_144,A_141,A_141,E_142,k2_funct_2(A_141,B_143)) = k5_relat_1(E_142,k2_funct_2(A_141,B_143))
      | ~ v1_funct_1(k2_funct_2(A_141,B_143))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144)))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_143,A_141,A_141)
      | ~ v1_funct_2(B_143,A_141,A_141)
      | ~ v1_funct_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_34,c_457])).

tff(c_1703,plain,(
    ! [A_141,B_143] :
      ( k1_partfun1('#skF_1','#skF_1',A_141,A_141,'#skF_2',k2_funct_2(A_141,B_143)) = k5_relat_1('#skF_2',k2_funct_2(A_141,B_143))
      | ~ v1_funct_1(k2_funct_2(A_141,B_143))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_143,A_141,A_141)
      | ~ v1_funct_2(B_143,A_141,A_141)
      | ~ v1_funct_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_50,c_1685])).

tff(c_1728,plain,(
    ! [A_146,B_147] :
      ( k1_partfun1('#skF_1','#skF_1',A_146,A_146,'#skF_2',k2_funct_2(A_146,B_147)) = k5_relat_1('#skF_2',k2_funct_2(A_146,B_147))
      | ~ v1_funct_1(k2_funct_2(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1703])).

tff(c_1746,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1728])).

tff(c_1769,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_318,c_317,c_317,c_317,c_1746])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_319,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_84])).

tff(c_1770,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_319])).

tff(c_1777,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1770])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_264,c_210,c_634,c_1777])).

tff(c_1781,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2017,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2014,c_1781])).

tff(c_2488,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2017])).

tff(c_2495,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2488])).

tff(c_2498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_1961,c_1918,c_1891,c_2495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.08  
% 5.64/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.08  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.64/2.08  
% 5.64/2.08  %Foreground sorts:
% 5.64/2.08  
% 5.64/2.08  
% 5.64/2.08  %Background operators:
% 5.64/2.08  
% 5.64/2.08  
% 5.64/2.08  %Foreground operators:
% 5.64/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.64/2.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.64/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.64/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.64/2.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.64/2.08  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.64/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.64/2.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.64/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.64/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.64/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.64/2.08  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.64/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.64/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.64/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.64/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.64/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.64/2.08  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.64/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.64/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.08  
% 5.64/2.11  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.64/2.11  tff(f_141, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.64/2.11  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.64/2.11  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.64/2.11  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.64/2.11  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.64/2.11  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.64/2.11  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.64/2.11  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.64/2.11  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.64/2.11  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.64/2.11  tff(f_106, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.64/2.11  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.64/2.11  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.64/2.11  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.64/2.11  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.64/2.11  tff(c_71, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.64/2.11  tff(c_77, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.64/2.11  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 5.64/2.11  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.64/2.11  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.64/2.11  tff(c_1951, plain, (![C_184, A_185, B_186]: (v2_funct_1(C_184) | ~v3_funct_2(C_184, A_185, B_186) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.64/2.11  tff(c_1957, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1951])).
% 5.64/2.11  tff(c_1961, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1957])).
% 5.64/2.11  tff(c_46, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.64/2.11  tff(c_22, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.64/2.11  tff(c_57, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 5.64/2.11  tff(c_1913, plain, (![A_177, B_178, D_179]: (r2_relset_1(A_177, B_178, D_179, D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.64/2.11  tff(c_1918, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_57, c_1913])).
% 5.64/2.11  tff(c_1784, plain, (![C_149, B_150, A_151]: (v5_relat_1(C_149, B_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.64/2.11  tff(c_1792, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1784])).
% 5.64/2.11  tff(c_1805, plain, (![B_158, A_159]: (k2_relat_1(B_158)=A_159 | ~v2_funct_2(B_158, A_159) | ~v5_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.64/2.11  tff(c_1811, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1792, c_1805])).
% 5.64/2.11  tff(c_1817, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1811])).
% 5.64/2.11  tff(c_1818, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1817])).
% 5.64/2.11  tff(c_1878, plain, (![C_172, B_173, A_174]: (v2_funct_2(C_172, B_173) | ~v3_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.64/2.11  tff(c_1884, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1878])).
% 5.64/2.11  tff(c_1888, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1884])).
% 5.64/2.11  tff(c_1890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1818, c_1888])).
% 5.64/2.11  tff(c_1891, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1817])).
% 5.64/2.11  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.64/2.11  tff(c_59, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 5.64/2.11  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.64/2.11  tff(c_2004, plain, (![A_198, B_199]: (k2_funct_2(A_198, B_199)=k2_funct_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.64/2.11  tff(c_2010, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2004])).
% 5.64/2.11  tff(c_2014, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2010])).
% 5.64/2.11  tff(c_1993, plain, (![A_196, B_197]: (v1_funct_1(k2_funct_2(A_196, B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.64/2.11  tff(c_1999, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1993])).
% 5.64/2.11  tff(c_2003, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1999])).
% 5.64/2.11  tff(c_2015, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2014, c_2003])).
% 5.64/2.11  tff(c_34, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.64/2.11  tff(c_2151, plain, (![C_211, D_215, A_216, B_214, F_212, E_213]: (k1_partfun1(A_216, B_214, C_211, D_215, E_213, F_212)=k5_relat_1(E_213, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_211, D_215))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_1(E_213))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.64/2.11  tff(c_2159, plain, (![A_216, B_214, E_213]: (k1_partfun1(A_216, B_214, '#skF_1', '#skF_1', E_213, '#skF_2')=k5_relat_1(E_213, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_1(E_213))), inference(resolution, [status(thm)], [c_50, c_2151])).
% 5.64/2.11  tff(c_2174, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_1', '#skF_1', E_219, '#skF_2')=k5_relat_1(E_219, '#skF_2') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2159])).
% 5.64/2.11  tff(c_2439, plain, (![A_227, B_228]: (k1_partfun1(A_227, A_227, '#skF_1', '#skF_1', k2_funct_2(A_227, B_228), '#skF_2')=k5_relat_1(k2_funct_2(A_227, B_228), '#skF_2') | ~v1_funct_1(k2_funct_2(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(k2_zfmisc_1(A_227, A_227))) | ~v3_funct_2(B_228, A_227, A_227) | ~v1_funct_2(B_228, A_227, A_227) | ~v1_funct_1(B_228))), inference(resolution, [status(thm)], [c_34, c_2174])).
% 5.64/2.11  tff(c_2449, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2439])).
% 5.64/2.11  tff(c_2460, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2015, c_2014, c_2014, c_2014, c_2449])).
% 5.64/2.11  tff(c_254, plain, (![C_75, A_76, B_77]: (v2_funct_1(C_75) | ~v3_funct_2(C_75, A_76, B_77) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.64/2.11  tff(c_260, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_254])).
% 5.64/2.11  tff(c_264, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_260])).
% 5.64/2.11  tff(c_205, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.64/2.11  tff(c_210, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_57, c_205])).
% 5.64/2.11  tff(c_307, plain, (![A_91, B_92]: (k2_funct_2(A_91, B_92)=k2_funct_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.64/2.11  tff(c_313, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_307])).
% 5.64/2.11  tff(c_317, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_313])).
% 5.64/2.11  tff(c_291, plain, (![A_87, B_88]: (v1_funct_1(k2_funct_2(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v3_funct_2(B_88, A_87, A_87) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.64/2.11  tff(c_297, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_291])).
% 5.64/2.11  tff(c_301, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_297])).
% 5.64/2.11  tff(c_318, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_301])).
% 5.64/2.11  tff(c_335, plain, (![A_97, B_98]: (v3_funct_2(k2_funct_2(A_97, B_98), A_97, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.64/2.11  tff(c_339, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_335])).
% 5.64/2.11  tff(c_343, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_317, c_339])).
% 5.64/2.11  tff(c_344, plain, (![A_99, B_100]: (m1_subset_1(k2_funct_2(A_99, B_100), k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.64/2.11  tff(c_374, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_317, c_344])).
% 5.64/2.11  tff(c_388, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_374])).
% 5.64/2.11  tff(c_24, plain, (![C_18, B_17, A_16]: (v2_funct_2(C_18, B_17) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.64/2.11  tff(c_401, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_388, c_24])).
% 5.64/2.11  tff(c_430, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_343, c_401])).
% 5.64/2.11  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.64/2.11  tff(c_415, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_388, c_2])).
% 5.64/2.11  tff(c_439, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_415])).
% 5.64/2.11  tff(c_14, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.64/2.11  tff(c_436, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_388, c_14])).
% 5.64/2.11  tff(c_32, plain, (![B_20, A_19]: (k2_relat_1(B_20)=A_19 | ~v2_funct_2(B_20, A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.64/2.11  tff(c_442, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_436, c_32])).
% 5.64/2.11  tff(c_445, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_442])).
% 5.64/2.11  tff(c_615, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_430, c_445])).
% 5.64/2.11  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.64/2.11  tff(c_622, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_615, c_6])).
% 5.64/2.11  tff(c_634, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_264, c_622])).
% 5.64/2.11  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.64/2.11  tff(c_58, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.64/2.11  tff(c_457, plain, (![B_104, F_102, A_106, C_101, D_105, E_103]: (k1_partfun1(A_106, B_104, C_101, D_105, E_103, F_102)=k5_relat_1(E_103, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_101, D_105))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_106, B_104))) | ~v1_funct_1(E_103))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.64/2.11  tff(c_1685, plain, (![B_144, A_141, A_145, B_143, E_142]: (k1_partfun1(A_145, B_144, A_141, A_141, E_142, k2_funct_2(A_141, B_143))=k5_relat_1(E_142, k2_funct_2(A_141, B_143)) | ~v1_funct_1(k2_funct_2(A_141, B_143)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))) | ~v1_funct_1(E_142) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_143, A_141, A_141) | ~v1_funct_2(B_143, A_141, A_141) | ~v1_funct_1(B_143))), inference(resolution, [status(thm)], [c_34, c_457])).
% 5.64/2.11  tff(c_1703, plain, (![A_141, B_143]: (k1_partfun1('#skF_1', '#skF_1', A_141, A_141, '#skF_2', k2_funct_2(A_141, B_143))=k5_relat_1('#skF_2', k2_funct_2(A_141, B_143)) | ~v1_funct_1(k2_funct_2(A_141, B_143)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_143, A_141, A_141) | ~v1_funct_2(B_143, A_141, A_141) | ~v1_funct_1(B_143))), inference(resolution, [status(thm)], [c_50, c_1685])).
% 5.64/2.11  tff(c_1728, plain, (![A_146, B_147]: (k1_partfun1('#skF_1', '#skF_1', A_146, A_146, '#skF_2', k2_funct_2(A_146, B_147))=k5_relat_1('#skF_2', k2_funct_2(A_146, B_147)) | ~v1_funct_1(k2_funct_2(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_147, A_146, A_146) | ~v1_funct_2(B_147, A_146, A_146) | ~v1_funct_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1703])).
% 5.64/2.11  tff(c_1746, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1728])).
% 5.64/2.11  tff(c_1769, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_318, c_317, c_317, c_317, c_1746])).
% 5.64/2.11  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.64/2.11  tff(c_84, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.64/2.11  tff(c_319, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_84])).
% 5.64/2.11  tff(c_1770, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_319])).
% 5.64/2.11  tff(c_1777, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1770])).
% 5.64/2.11  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_264, c_210, c_634, c_1777])).
% 5.64/2.11  tff(c_1781, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 5.64/2.11  tff(c_2017, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2014, c_1781])).
% 5.64/2.11  tff(c_2488, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2017])).
% 5.64/2.11  tff(c_2495, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_2488])).
% 5.64/2.11  tff(c_2498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_1961, c_1918, c_1891, c_2495])).
% 5.64/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.11  
% 5.64/2.11  Inference rules
% 5.64/2.11  ----------------------
% 5.64/2.11  #Ref     : 0
% 5.64/2.11  #Sup     : 507
% 5.64/2.11  #Fact    : 0
% 5.64/2.11  #Define  : 0
% 5.64/2.11  #Split   : 4
% 5.64/2.11  #Chain   : 0
% 5.64/2.11  #Close   : 0
% 5.64/2.11  
% 5.64/2.11  Ordering : KBO
% 5.64/2.11  
% 5.64/2.11  Simplification rules
% 5.64/2.11  ----------------------
% 5.64/2.11  #Subsume      : 1
% 5.64/2.11  #Demod        : 1296
% 5.64/2.11  #Tautology    : 214
% 5.64/2.11  #SimpNegUnit  : 2
% 5.64/2.11  #BackRed      : 43
% 5.64/2.11  
% 5.64/2.11  #Partial instantiations: 0
% 5.64/2.11  #Strategies tried      : 1
% 5.64/2.11  
% 5.64/2.11  Timing (in seconds)
% 5.64/2.11  ----------------------
% 5.64/2.11  Preprocessing        : 0.36
% 5.64/2.11  Parsing              : 0.19
% 5.64/2.11  CNF conversion       : 0.02
% 5.64/2.11  Main loop            : 0.96
% 5.64/2.11  Inferencing          : 0.33
% 5.64/2.11  Reduction            : 0.35
% 5.64/2.11  Demodulation         : 0.27
% 5.64/2.11  BG Simplification    : 0.03
% 5.64/2.11  Subsumption          : 0.17
% 5.64/2.11  Abstraction          : 0.04
% 5.64/2.11  MUC search           : 0.00
% 5.64/2.11  Cooper               : 0.00
% 5.64/2.12  Total                : 1.37
% 5.64/2.12  Index Insertion      : 0.00
% 5.64/2.12  Index Deletion       : 0.00
% 5.64/2.12  Index Matching       : 0.00
% 5.64/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
