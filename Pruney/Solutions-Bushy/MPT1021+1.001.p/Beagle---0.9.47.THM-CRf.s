%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1021+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:16 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 339 expanded)
%              Number of leaves         :   41 ( 147 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 (1049 expanded)
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

tff(f_139,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_100,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_70,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_70,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_78,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2028,plain,(
    ! [C_190,A_191,B_192] :
      ( v2_funct_1(C_190)
      | ~ v3_funct_2(C_190,A_191,B_192)
      | ~ v1_funct_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2034,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2028])).

tff(c_2038,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2034])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1915,plain,(
    ! [A_167,B_168,D_169] :
      ( r2_relset_1(A_167,B_168,D_169,D_169)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1920,plain,(
    ! [A_14] : r2_relset_1(A_14,A_14,k6_partfun1(A_14),k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_28,c_1915])).

tff(c_1894,plain,(
    ! [C_158,B_159,A_160] :
      ( v5_relat_1(C_158,B_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1902,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1894])).

tff(c_1923,plain,(
    ! [B_171,A_172] :
      ( k2_relat_1(B_171) = A_172
      | ~ v2_funct_2(B_171,A_172)
      | ~ v5_relat_1(B_171,A_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1929,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1902,c_1923])).

tff(c_1935,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1929])).

tff(c_1936,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1935])).

tff(c_1990,plain,(
    ! [C_184,B_185,A_186] :
      ( v2_funct_2(C_184,B_185)
      | ~ v3_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1996,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1990])).

tff(c_2000,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1996])).

tff(c_2002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1936,c_2000])).

tff(c_2003,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1935])).

tff(c_36,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_relat_1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_58,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_partfun1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2131,plain,(
    ! [A_211,B_212] :
      ( k2_funct_2(A_211,B_212) = k2_funct_1(B_212)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_zfmisc_1(A_211,A_211)))
      | ~ v3_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2137,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2131])).

tff(c_2141,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2137])).

tff(c_2120,plain,(
    ! [A_209,B_210] :
      ( v1_funct_1(k2_funct_2(A_209,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v3_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2126,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2120])).

tff(c_2130,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2126])).

tff(c_2142,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2141,c_2130])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_funct_2(A_12,B_13),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12)))
      | ~ v3_funct_2(B_13,A_12,A_12)
      | ~ v1_funct_2(B_13,A_12,A_12)
      | ~ v1_funct_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2289,plain,(
    ! [E_227,A_228,B_225,C_223,D_224,F_226] :
      ( k1_partfun1(A_228,B_225,C_223,D_224,E_227,F_226) = k5_relat_1(E_227,F_226)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_223,D_224)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_225)))
      | ~ v1_funct_1(E_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2297,plain,(
    ! [A_228,B_225,E_227] :
      ( k1_partfun1(A_228,B_225,'#skF_1','#skF_1',E_227,'#skF_2') = k5_relat_1(E_227,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_225)))
      | ~ v1_funct_1(E_227) ) ),
    inference(resolution,[status(thm)],[c_50,c_2289])).

tff(c_2312,plain,(
    ! [A_229,B_230,E_231] :
      ( k1_partfun1(A_229,B_230,'#skF_1','#skF_1',E_231,'#skF_2') = k5_relat_1(E_231,'#skF_2')
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_1(E_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2297])).

tff(c_2545,plain,(
    ! [A_239,B_240] :
      ( k1_partfun1(A_239,A_239,'#skF_1','#skF_1',k2_funct_2(A_239,B_240),'#skF_2') = k5_relat_1(k2_funct_2(A_239,B_240),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_239,B_240))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_1(B_240) ) ),
    inference(resolution,[status(thm)],[c_18,c_2312])).

tff(c_2555,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2545])).

tff(c_2566,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2142,c_2141,c_2141,c_2141,c_2555])).

tff(c_243,plain,(
    ! [C_77,A_78,B_79] :
      ( v2_funct_1(C_77)
      | ~ v3_funct_2(C_77,A_78,B_79)
      | ~ v1_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_249,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_243])).

tff(c_253,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_249])).

tff(c_102,plain,(
    ! [A_50,B_51,D_52] :
      ( r2_relset_1(A_50,B_51,D_52,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [A_14] : r2_relset_1(A_14,A_14,k6_partfun1(A_14),k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_192,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_200,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_192])).

tff(c_266,plain,(
    ! [A_84,B_85] :
      ( k1_relset_1(A_84,A_84,B_85) = A_84
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84)))
      | ~ v1_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_272,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_266])).

tff(c_277,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_200,c_272])).

tff(c_44,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_57,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_partfun1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_314,plain,(
    ! [A_95,B_96] :
      ( k2_funct_2(A_95,B_96) = k2_funct_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_320,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_314])).

tff(c_324,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_320])).

tff(c_302,plain,(
    ! [A_92,B_93] :
      ( v1_funct_1(k2_funct_2(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_308,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_302])).

tff(c_312,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_308])).

tff(c_325,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_312])).

tff(c_462,plain,(
    ! [A_111,B_108,F_109,E_110,D_107,C_106] :
      ( k1_partfun1(A_111,B_108,C_106,D_107,E_110,F_109) = k5_relat_1(E_110,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_106,D_107)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_108)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1674,plain,(
    ! [A_152,B_149,A_150,E_153,B_151] :
      ( k1_partfun1(A_152,B_151,A_150,A_150,E_153,k2_funct_2(A_150,B_149)) = k5_relat_1(E_153,k2_funct_2(A_150,B_149))
      | ~ v1_funct_1(k2_funct_2(A_150,B_149))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151)))
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1(A_150,A_150)))
      | ~ v3_funct_2(B_149,A_150,A_150)
      | ~ v1_funct_2(B_149,A_150,A_150)
      | ~ v1_funct_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_18,c_462])).

tff(c_1690,plain,(
    ! [A_150,B_149] :
      ( k1_partfun1('#skF_1','#skF_1',A_150,A_150,'#skF_2',k2_funct_2(A_150,B_149)) = k5_relat_1('#skF_2',k2_funct_2(A_150,B_149))
      | ~ v1_funct_1(k2_funct_2(A_150,B_149))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1(A_150,A_150)))
      | ~ v3_funct_2(B_149,A_150,A_150)
      | ~ v1_funct_2(B_149,A_150,A_150)
      | ~ v1_funct_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_50,c_1674])).

tff(c_1827,plain,(
    ! [A_154,B_155] :
      ( k1_partfun1('#skF_1','#skF_1',A_154,A_154,'#skF_2',k2_funct_2(A_154,B_155)) = k5_relat_1('#skF_2',k2_funct_2(A_154,B_155))
      | ~ v1_funct_1(k2_funct_2(A_154,B_155))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(A_154,A_154)))
      | ~ v3_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1690])).

tff(c_1845,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1827])).

tff(c_1868,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_325,c_324,c_324,c_324,c_1845])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_326,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_79])).

tff(c_1880,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_326])).

tff(c_1887,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1880])).

tff(c_1890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_253,c_107,c_277,c_1887])).

tff(c_1891,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2144,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2141,c_1891])).

tff(c_2595,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_2144])).

tff(c_2602,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2595])).

tff(c_2605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_2038,c_1920,c_2003,c_2602])).

%------------------------------------------------------------------------------
