%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.11s
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

tff(f_140,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_93,axiom,(
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

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_70,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1918,plain,(
    ! [C_195,A_196,B_197] :
      ( v2_funct_1(C_195)
      | ~ v3_funct_2(C_195,A_196,B_197)
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1924,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1918])).

tff(c_1928,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1924])).

tff(c_38,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1888,plain,(
    ! [A_187,B_188,D_189] :
      ( r2_relset_1(A_187,B_188,D_189,D_189)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1893,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_1888])).

tff(c_1766,plain,(
    ! [C_157,B_158,A_159] :
      ( v5_relat_1(C_157,B_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1774,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1766])).

tff(c_1787,plain,(
    ! [B_166,A_167] :
      ( k2_relat_1(B_166) = A_167
      | ~ v2_funct_2(B_166,A_167)
      | ~ v5_relat_1(B_166,A_167)
      | ~ v1_relat_1(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1793,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1774,c_1787])).

tff(c_1799,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1793])).

tff(c_1800,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1799])).

tff(c_1862,plain,(
    ! [C_183,B_184,A_185] :
      ( v2_funct_2(C_183,B_184)
      | ~ v3_funct_2(C_183,A_185,B_184)
      | ~ v1_funct_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1868,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1862])).

tff(c_1872,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1868])).

tff(c_1874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1800,c_1872])).

tff(c_1875,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1799])).

tff(c_44,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2012,plain,(
    ! [A_215,B_216] :
      ( k2_funct_2(A_215,B_216) = k2_funct_1(B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2018,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2012])).

tff(c_2022,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2018])).

tff(c_2000,plain,(
    ! [A_212,B_213] :
      ( v1_funct_1(k2_funct_2(A_212,B_213))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k2_zfmisc_1(A_212,A_212)))
      | ~ v3_funct_2(B_213,A_212,A_212)
      | ~ v1_funct_2(B_213,A_212,A_212)
      | ~ v1_funct_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2006,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2000])).

tff(c_2010,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2006])).

tff(c_2032,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_2010])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2178,plain,(
    ! [E_227,A_230,C_225,B_228,D_229,F_226] :
      ( k1_partfun1(A_230,B_228,C_225,D_229,E_227,F_226) = k5_relat_1(E_227,F_226)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_225,D_229)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_230,B_228)))
      | ~ v1_funct_1(E_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2186,plain,(
    ! [A_230,B_228,E_227] :
      ( k1_partfun1(A_230,B_228,'#skF_1','#skF_1',E_227,'#skF_2') = k5_relat_1(E_227,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_230,B_228)))
      | ~ v1_funct_1(E_227) ) ),
    inference(resolution,[status(thm)],[c_50,c_2178])).

tff(c_2212,plain,(
    ! [A_231,B_232,E_233] :
      ( k1_partfun1(A_231,B_232,'#skF_1','#skF_1',E_233,'#skF_2') = k5_relat_1(E_233,'#skF_2')
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(E_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2186])).

tff(c_2458,plain,(
    ! [A_238,B_239] :
      ( k1_partfun1(A_238,A_238,'#skF_1','#skF_1',k2_funct_2(A_238,B_239),'#skF_2') = k5_relat_1(k2_funct_2(A_238,B_239),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_238,B_239))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_zfmisc_1(A_238,A_238)))
      | ~ v3_funct_2(B_239,A_238,A_238)
      | ~ v1_funct_2(B_239,A_238,A_238)
      | ~ v1_funct_1(B_239) ) ),
    inference(resolution,[status(thm)],[c_28,c_2212])).

tff(c_2470,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2458])).

tff(c_2484,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2032,c_2022,c_2022,c_2022,c_2470])).

tff(c_243,plain,(
    ! [C_77,A_78,B_79] :
      ( v2_funct_1(C_77)
      | ~ v3_funct_2(C_77,A_78,B_79)
      | ~ v1_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_192,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_192])).

tff(c_266,plain,(
    ! [A_84,B_85] :
      ( k1_relset_1(A_84,A_84,B_85) = A_84
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84)))
      | ~ v1_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_272,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_266])).

tff(c_277,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_200,c_272])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_314,plain,(
    ! [A_95,B_96] :
      ( k2_funct_2(A_95,B_96) = k2_funct_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

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
    inference(cnfTransformation,[status(thm)],[f_93])).

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
    ! [E_108,A_111,F_107,B_109,C_106,D_110] :
      ( k1_partfun1(A_111,B_109,C_106,D_110,E_108,F_107) = k5_relat_1(E_108,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_106,D_110)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1674,plain,(
    ! [A_152,B_150,E_149,B_153,A_151] :
      ( k1_partfun1(A_151,B_153,A_152,A_152,E_149,k2_funct_2(A_152,B_150)) = k5_relat_1(E_149,k2_funct_2(A_152,B_150))
      | ~ v1_funct_1(k2_funct_2(A_152,B_150))
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_153)))
      | ~ v1_funct_1(E_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v3_funct_2(B_150,A_152,A_152)
      | ~ v1_funct_2(B_150,A_152,A_152)
      | ~ v1_funct_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_28,c_462])).

tff(c_1690,plain,(
    ! [A_152,B_150] :
      ( k1_partfun1('#skF_1','#skF_1',A_152,A_152,'#skF_2',k2_funct_2(A_152,B_150)) = k5_relat_1('#skF_2',k2_funct_2(A_152,B_150))
      | ~ v1_funct_1(k2_funct_2(A_152,B_150))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v3_funct_2(B_150,A_152,A_152)
      | ~ v1_funct_2(B_150,A_152,A_152)
      | ~ v1_funct_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_50,c_1674])).

tff(c_1715,plain,(
    ! [A_154,B_155] :
      ( k1_partfun1('#skF_1','#skF_1',A_154,A_154,'#skF_2',k2_funct_2(A_154,B_155)) = k5_relat_1('#skF_2',k2_funct_2(A_154,B_155))
      | ~ v1_funct_1(k2_funct_2(A_154,B_155))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(A_154,A_154)))
      | ~ v3_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1690])).

tff(c_1731,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1715])).

tff(c_1751,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_325,c_324,c_324,c_324,c_1731])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_326,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_79])).

tff(c_1752,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_326])).

tff(c_1759,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1752])).

tff(c_1762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_253,c_107,c_277,c_1759])).

tff(c_1763,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2033,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_1763])).

tff(c_2528,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2484,c_2033])).

tff(c_2535,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2528])).

tff(c_2538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_1928,c_1893,c_1875,c_2535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.93  
% 5.11/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.93  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.11/1.93  
% 5.11/1.93  %Foreground sorts:
% 5.11/1.93  
% 5.11/1.93  
% 5.11/1.93  %Background operators:
% 5.11/1.93  
% 5.11/1.93  
% 5.11/1.93  %Foreground operators:
% 5.11/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/1.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.11/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.93  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.11/1.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.11/1.93  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.11/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.11/1.93  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.11/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.11/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.11/1.93  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.11/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.11/1.93  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.11/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.11/1.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.11/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.93  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.11/1.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.11/1.93  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.11/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/1.93  
% 5.11/1.96  tff(f_140, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.11/1.96  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.11/1.96  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.11/1.96  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.11/1.96  tff(f_57, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.11/1.96  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.11/1.96  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.11/1.96  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.11/1.96  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.11/1.96  tff(f_117, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.11/1.96  tff(f_93, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.11/1.96  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.11/1.96  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.11/1.96  tff(f_127, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.11/1.96  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.11/1.96  tff(c_70, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.11/1.96  tff(c_78, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_70])).
% 5.11/1.96  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.11/1.96  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.11/1.96  tff(c_1918, plain, (![C_195, A_196, B_197]: (v2_funct_1(C_195) | ~v3_funct_2(C_195, A_196, B_197) | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.11/1.96  tff(c_1924, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1918])).
% 5.11/1.96  tff(c_1928, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1924])).
% 5.11/1.96  tff(c_38, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.11/1.96  tff(c_1888, plain, (![A_187, B_188, D_189]: (r2_relset_1(A_187, B_188, D_189, D_189) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.11/1.96  tff(c_1893, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_1888])).
% 5.11/1.96  tff(c_1766, plain, (![C_157, B_158, A_159]: (v5_relat_1(C_157, B_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.11/1.96  tff(c_1774, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1766])).
% 5.11/1.96  tff(c_1787, plain, (![B_166, A_167]: (k2_relat_1(B_166)=A_167 | ~v2_funct_2(B_166, A_167) | ~v5_relat_1(B_166, A_167) | ~v1_relat_1(B_166))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.96  tff(c_1793, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1774, c_1787])).
% 5.11/1.96  tff(c_1799, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1793])).
% 5.11/1.96  tff(c_1800, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1799])).
% 5.11/1.96  tff(c_1862, plain, (![C_183, B_184, A_185]: (v2_funct_2(C_183, B_184) | ~v3_funct_2(C_183, A_185, B_184) | ~v1_funct_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.11/1.96  tff(c_1868, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1862])).
% 5.11/1.96  tff(c_1872, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1868])).
% 5.11/1.96  tff(c_1874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1800, c_1872])).
% 5.11/1.96  tff(c_1875, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1799])).
% 5.11/1.96  tff(c_44, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.11/1.96  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.11/1.96  tff(c_58, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2])).
% 5.11/1.96  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.11/1.96  tff(c_2012, plain, (![A_215, B_216]: (k2_funct_2(A_215, B_216)=k2_funct_1(B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.11/1.96  tff(c_2018, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2012])).
% 5.11/1.96  tff(c_2022, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2018])).
% 5.11/1.96  tff(c_2000, plain, (![A_212, B_213]: (v1_funct_1(k2_funct_2(A_212, B_213)) | ~m1_subset_1(B_213, k1_zfmisc_1(k2_zfmisc_1(A_212, A_212))) | ~v3_funct_2(B_213, A_212, A_212) | ~v1_funct_2(B_213, A_212, A_212) | ~v1_funct_1(B_213))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.11/1.96  tff(c_2006, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2000])).
% 5.11/1.96  tff(c_2010, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2006])).
% 5.11/1.96  tff(c_2032, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_2010])).
% 5.11/1.96  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.11/1.96  tff(c_2178, plain, (![E_227, A_230, C_225, B_228, D_229, F_226]: (k1_partfun1(A_230, B_228, C_225, D_229, E_227, F_226)=k5_relat_1(E_227, F_226) | ~m1_subset_1(F_226, k1_zfmisc_1(k2_zfmisc_1(C_225, D_229))) | ~v1_funct_1(F_226) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_230, B_228))) | ~v1_funct_1(E_227))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.11/1.96  tff(c_2186, plain, (![A_230, B_228, E_227]: (k1_partfun1(A_230, B_228, '#skF_1', '#skF_1', E_227, '#skF_2')=k5_relat_1(E_227, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_230, B_228))) | ~v1_funct_1(E_227))), inference(resolution, [status(thm)], [c_50, c_2178])).
% 5.11/1.96  tff(c_2212, plain, (![A_231, B_232, E_233]: (k1_partfun1(A_231, B_232, '#skF_1', '#skF_1', E_233, '#skF_2')=k5_relat_1(E_233, '#skF_2') | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(E_233))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2186])).
% 5.11/1.96  tff(c_2458, plain, (![A_238, B_239]: (k1_partfun1(A_238, A_238, '#skF_1', '#skF_1', k2_funct_2(A_238, B_239), '#skF_2')=k5_relat_1(k2_funct_2(A_238, B_239), '#skF_2') | ~v1_funct_1(k2_funct_2(A_238, B_239)) | ~m1_subset_1(B_239, k1_zfmisc_1(k2_zfmisc_1(A_238, A_238))) | ~v3_funct_2(B_239, A_238, A_238) | ~v1_funct_2(B_239, A_238, A_238) | ~v1_funct_1(B_239))), inference(resolution, [status(thm)], [c_28, c_2212])).
% 5.11/1.96  tff(c_2470, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2458])).
% 5.11/1.96  tff(c_2484, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2032, c_2022, c_2022, c_2022, c_2470])).
% 5.11/1.96  tff(c_243, plain, (![C_77, A_78, B_79]: (v2_funct_1(C_77) | ~v3_funct_2(C_77, A_78, B_79) | ~v1_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.11/1.96  tff(c_249, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_243])).
% 5.11/1.96  tff(c_253, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_249])).
% 5.11/1.96  tff(c_102, plain, (![A_50, B_51, D_52]: (r2_relset_1(A_50, B_51, D_52, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.11/1.96  tff(c_107, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_102])).
% 5.11/1.96  tff(c_192, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.11/1.96  tff(c_200, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_192])).
% 5.11/1.96  tff(c_266, plain, (![A_84, B_85]: (k1_relset_1(A_84, A_84, B_85)=A_84 | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(A_84, A_84))) | ~v1_funct_2(B_85, A_84, A_84) | ~v1_funct_1(B_85))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.11/1.96  tff(c_272, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_266])).
% 5.11/1.96  tff(c_277, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_200, c_272])).
% 5.11/1.96  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.11/1.96  tff(c_57, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 5.11/1.96  tff(c_314, plain, (![A_95, B_96]: (k2_funct_2(A_95, B_96)=k2_funct_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.11/1.96  tff(c_320, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_314])).
% 5.11/1.96  tff(c_324, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_320])).
% 5.11/1.96  tff(c_302, plain, (![A_92, B_93]: (v1_funct_1(k2_funct_2(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.11/1.96  tff(c_308, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_302])).
% 5.11/1.96  tff(c_312, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_308])).
% 5.11/1.96  tff(c_325, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_312])).
% 5.11/1.96  tff(c_462, plain, (![E_108, A_111, F_107, B_109, C_106, D_110]: (k1_partfun1(A_111, B_109, C_106, D_110, E_108, F_107)=k5_relat_1(E_108, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_106, D_110))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.11/1.96  tff(c_1674, plain, (![A_152, B_150, E_149, B_153, A_151]: (k1_partfun1(A_151, B_153, A_152, A_152, E_149, k2_funct_2(A_152, B_150))=k5_relat_1(E_149, k2_funct_2(A_152, B_150)) | ~v1_funct_1(k2_funct_2(A_152, B_150)) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_153))) | ~v1_funct_1(E_149) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v3_funct_2(B_150, A_152, A_152) | ~v1_funct_2(B_150, A_152, A_152) | ~v1_funct_1(B_150))), inference(resolution, [status(thm)], [c_28, c_462])).
% 5.11/1.96  tff(c_1690, plain, (![A_152, B_150]: (k1_partfun1('#skF_1', '#skF_1', A_152, A_152, '#skF_2', k2_funct_2(A_152, B_150))=k5_relat_1('#skF_2', k2_funct_2(A_152, B_150)) | ~v1_funct_1(k2_funct_2(A_152, B_150)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v3_funct_2(B_150, A_152, A_152) | ~v1_funct_2(B_150, A_152, A_152) | ~v1_funct_1(B_150))), inference(resolution, [status(thm)], [c_50, c_1674])).
% 5.11/1.96  tff(c_1715, plain, (![A_154, B_155]: (k1_partfun1('#skF_1', '#skF_1', A_154, A_154, '#skF_2', k2_funct_2(A_154, B_155))=k5_relat_1('#skF_2', k2_funct_2(A_154, B_155)) | ~v1_funct_1(k2_funct_2(A_154, B_155)) | ~m1_subset_1(B_155, k1_zfmisc_1(k2_zfmisc_1(A_154, A_154))) | ~v3_funct_2(B_155, A_154, A_154) | ~v1_funct_2(B_155, A_154, A_154) | ~v1_funct_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1690])).
% 5.11/1.96  tff(c_1731, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1715])).
% 5.11/1.96  tff(c_1751, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_325, c_324, c_324, c_324, c_1731])).
% 5.11/1.96  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.11/1.96  tff(c_79, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.11/1.96  tff(c_326, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_79])).
% 5.11/1.96  tff(c_1752, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_326])).
% 5.11/1.96  tff(c_1759, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1752])).
% 5.11/1.96  tff(c_1762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_253, c_107, c_277, c_1759])).
% 5.11/1.96  tff(c_1763, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 5.11/1.96  tff(c_2033, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_1763])).
% 5.11/1.96  tff(c_2528, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2484, c_2033])).
% 5.11/1.96  tff(c_2535, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2528])).
% 5.11/1.96  tff(c_2538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_1928, c_1893, c_1875, c_2535])).
% 5.11/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.96  
% 5.11/1.96  Inference rules
% 5.11/1.96  ----------------------
% 5.11/1.96  #Ref     : 0
% 5.11/1.96  #Sup     : 537
% 5.11/1.96  #Fact    : 0
% 5.11/1.96  #Define  : 0
% 5.11/1.96  #Split   : 4
% 5.11/1.96  #Chain   : 0
% 5.11/1.96  #Close   : 0
% 5.11/1.96  
% 5.11/1.96  Ordering : KBO
% 5.11/1.96  
% 5.11/1.96  Simplification rules
% 5.11/1.96  ----------------------
% 5.11/1.96  #Subsume      : 0
% 5.11/1.96  #Demod        : 1247
% 5.11/1.96  #Tautology    : 222
% 5.11/1.96  #SimpNegUnit  : 2
% 5.11/1.96  #BackRed      : 48
% 5.11/1.96  
% 5.11/1.96  #Partial instantiations: 0
% 5.11/1.96  #Strategies tried      : 1
% 5.11/1.96  
% 5.11/1.96  Timing (in seconds)
% 5.11/1.96  ----------------------
% 5.11/1.96  Preprocessing        : 0.34
% 5.11/1.96  Parsing              : 0.19
% 5.11/1.96  CNF conversion       : 0.02
% 5.11/1.96  Main loop            : 0.84
% 5.11/1.96  Inferencing          : 0.30
% 5.11/1.96  Reduction            : 0.31
% 5.11/1.96  Demodulation         : 0.24
% 5.11/1.96  BG Simplification    : 0.03
% 5.11/1.96  Subsumption          : 0.14
% 5.11/1.96  Abstraction          : 0.04
% 5.11/1.96  MUC search           : 0.00
% 5.11/1.96  Cooper               : 0.00
% 5.11/1.96  Total                : 1.24
% 5.11/1.96  Index Insertion      : 0.00
% 5.11/1.96  Index Deletion       : 0.00
% 5.11/1.96  Index Matching       : 0.00
% 5.11/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
