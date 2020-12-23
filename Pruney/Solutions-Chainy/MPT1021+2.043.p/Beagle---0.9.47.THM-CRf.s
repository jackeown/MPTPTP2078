%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 384 expanded)
%              Number of leaves         :   43 ( 157 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 (1110 expanded)
%              Number of equality atoms :   65 ( 108 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_144,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_61,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_996,plain,(
    ! [C_241,A_242,B_243] :
      ( v2_funct_1(C_241)
      | ~ v3_funct_2(C_241,A_242,B_243)
      | ~ v1_funct_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1002,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_996])).

tff(c_1006,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1002])).

tff(c_32,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_942,plain,(
    ! [A_228,B_229,D_230] :
      ( r2_relset_1(A_228,B_229,D_230,D_230)
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_947,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_32,c_942])).

tff(c_800,plain,(
    ! [C_196,B_197,A_198] :
      ( v5_relat_1(C_196,B_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_808,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_800])).

tff(c_821,plain,(
    ! [B_205,A_206] :
      ( k2_relat_1(B_205) = A_206
      | ~ v2_funct_2(B_205,A_206)
      | ~ v5_relat_1(B_205,A_206)
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_827,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_808,c_821])).

tff(c_833,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_827])).

tff(c_834,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_917,plain,(
    ! [C_225,B_226,A_227] :
      ( v2_funct_2(C_225,B_226)
      | ~ v3_funct_2(C_225,A_227,B_226)
      | ~ v1_funct_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_923,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_917])).

tff(c_927,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_923])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_927])).

tff(c_930,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_38,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_951,plain,(
    ! [A_233,B_234,C_235] :
      ( k2_relset_1(A_233,B_234,C_235) = k2_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_957,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_951])).

tff(c_960,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_957])).

tff(c_1100,plain,(
    ! [C_260,A_261,B_262] :
      ( v1_funct_1(k2_funct_1(C_260))
      | k2_relset_1(A_261,B_262,C_260) != B_262
      | ~ v2_funct_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(C_260,A_261,B_262)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1106,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1100])).

tff(c_1111,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1006,c_960,c_1106])).

tff(c_40,plain,(
    ! [C_35,B_34,A_33] :
      ( m1_subset_1(k2_funct_1(C_35),k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ v2_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1196,plain,(
    ! [E_278,A_280,F_279,B_277,D_281,C_276] :
      ( k1_partfun1(A_280,B_277,C_276,D_281,E_278,F_279) = k5_relat_1(E_278,F_279)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_276,D_281)))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_277)))
      | ~ v1_funct_1(E_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1202,plain,(
    ! [A_280,B_277,E_278] :
      ( k1_partfun1(A_280,B_277,'#skF_1','#skF_1',E_278,'#skF_2') = k5_relat_1(E_278,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_277)))
      | ~ v1_funct_1(E_278) ) ),
    inference(resolution,[status(thm)],[c_50,c_1196])).

tff(c_1208,plain,(
    ! [A_282,B_283,E_284] :
      ( k1_partfun1(A_282,B_283,'#skF_1','#skF_1',E_284,'#skF_2') = k5_relat_1(E_284,'#skF_2')
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(E_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1202])).

tff(c_1268,plain,(
    ! [B_296,A_297,C_298] :
      ( k1_partfun1(B_296,A_297,'#skF_1','#skF_1',k2_funct_1(C_298),'#skF_2') = k5_relat_1(k2_funct_1(C_298),'#skF_2')
      | ~ v1_funct_1(k2_funct_1(C_298))
      | k2_relset_1(A_297,B_296,C_298) != B_296
      | ~ v2_funct_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296)))
      | ~ v1_funct_2(C_298,A_297,B_296)
      | ~ v1_funct_1(C_298) ) ),
    inference(resolution,[status(thm)],[c_40,c_1208])).

tff(c_1277,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1268])).

tff(c_1283,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1006,c_960,c_1111,c_1277])).

tff(c_1078,plain,(
    ! [A_258,B_259] :
      ( k2_funct_2(A_258,B_259) = k2_funct_1(B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ v3_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1084,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1078])).

tff(c_1088,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1084])).

tff(c_277,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_283,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_277])).

tff(c_287,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_283])).

tff(c_223,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_relset_1(A_77,B_78,D_79,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_228,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_32,c_223])).

tff(c_232,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_240,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_232])).

tff(c_318,plain,(
    ! [A_99,B_100] :
      ( k1_relset_1(A_99,A_99,B_100) = A_99
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_324,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_318])).

tff(c_329,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_240,c_324])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_81,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_102,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(B_54) = A_55
      | ~ v2_funct_2(B_54,A_55)
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_102])).

tff(c_114,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_108])).

tff(c_115,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_198,plain,(
    ! [C_74,B_75,A_76] :
      ( v2_funct_2(C_74,B_75)
      | ~ v3_funct_2(C_74,A_76,B_75)
      | ~ v1_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_204,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_198])).

tff(c_208,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_204])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_208])).

tff(c_211,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_245,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_251,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_254,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_251])).

tff(c_371,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_funct_1(k2_funct_1(C_110))
      | k2_relset_1(A_111,B_112,C_110) != B_112
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(C_110,A_111,B_112)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_377,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_371])).

tff(c_382,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_287,c_254,c_377])).

tff(c_422,plain,(
    ! [C_128,B_129,A_130] :
      ( m1_subset_1(k2_funct_1(C_128),k1_zfmisc_1(k2_zfmisc_1(B_129,A_130)))
      | k2_relset_1(A_130,B_129,C_128) != B_129
      | ~ v2_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(C_128,A_130,B_129)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29) = k5_relat_1(E_28,F_29)
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_758,plain,(
    ! [E_188,A_190,B_189,A_186,C_191,B_187] :
      ( k1_partfun1(A_190,B_187,B_189,A_186,E_188,k2_funct_1(C_191)) = k5_relat_1(E_188,k2_funct_1(C_191))
      | ~ v1_funct_1(k2_funct_1(C_191))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_190,B_187)))
      | ~ v1_funct_1(E_188)
      | k2_relset_1(A_186,B_189,C_191) != B_189
      | ~ v2_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_186,B_189)))
      | ~ v1_funct_2(C_191,A_186,B_189)
      | ~ v1_funct_1(C_191) ) ),
    inference(resolution,[status(thm)],[c_422,c_34])).

tff(c_764,plain,(
    ! [B_189,A_186,C_191] :
      ( k1_partfun1('#skF_1','#skF_1',B_189,A_186,'#skF_2',k2_funct_1(C_191)) = k5_relat_1('#skF_2',k2_funct_1(C_191))
      | ~ v1_funct_1(k2_funct_1(C_191))
      | ~ v1_funct_1('#skF_2')
      | k2_relset_1(A_186,B_189,C_191) != B_189
      | ~ v2_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_186,B_189)))
      | ~ v1_funct_2(C_191,A_186,B_189)
      | ~ v1_funct_1(C_191) ) ),
    inference(resolution,[status(thm)],[c_50,c_758])).

tff(c_770,plain,(
    ! [B_192,A_193,C_194] :
      ( k1_partfun1('#skF_1','#skF_1',B_192,A_193,'#skF_2',k2_funct_1(C_194)) = k5_relat_1('#skF_2',k2_funct_1(C_194))
      | ~ v1_funct_1(k2_funct_1(C_194))
      | k2_relset_1(A_193,B_192,C_194) != B_192
      | ~ v2_funct_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192)))
      | ~ v1_funct_2(C_194,A_193,B_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_764])).

tff(c_779,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_770])).

tff(c_785,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_287,c_254,c_382,c_779])).

tff(c_354,plain,(
    ! [A_107,B_108] :
      ( k2_funct_2(A_107,B_108) = k2_funct_1(B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v3_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_360,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_354])).

tff(c_364,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_360])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_365,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_79])).

tff(c_786,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_365])).

tff(c_793,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_786])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_287,c_228,c_329,c_793])).

tff(c_797,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1089,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_797])).

tff(c_1284,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_1089])).

tff(c_1291,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1284])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_1006,c_947,c_930,c_1291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.73  
% 3.99/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.73  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.99/1.73  
% 3.99/1.73  %Foreground sorts:
% 3.99/1.73  
% 3.99/1.73  
% 3.99/1.73  %Background operators:
% 3.99/1.73  
% 3.99/1.73  
% 3.99/1.73  %Foreground operators:
% 3.99/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.99/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.99/1.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.99/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.99/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.73  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.99/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.99/1.73  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.99/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.99/1.73  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.99/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.73  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.99/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.99/1.73  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.99/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.99/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.99/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.73  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.99/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.99/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.99/1.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.99/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.99/1.73  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.99/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.99/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.73  
% 4.30/1.76  tff(f_144, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 4.30/1.76  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.30/1.76  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.30/1.76  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.30/1.76  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.30/1.76  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.30/1.76  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.30/1.76  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.30/1.76  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.30/1.76  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.30/1.76  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.30/1.76  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.30/1.76  tff(f_105, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.30/1.76  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.30/1.76  tff(f_131, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 4.30/1.76  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.30/1.76  tff(c_70, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.76  tff(c_78, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_70])).
% 4.30/1.76  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.30/1.76  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.30/1.76  tff(c_996, plain, (![C_241, A_242, B_243]: (v2_funct_1(C_241) | ~v3_funct_2(C_241, A_242, B_243) | ~v1_funct_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.76  tff(c_1002, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_996])).
% 4.30/1.76  tff(c_1006, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1002])).
% 4.30/1.76  tff(c_32, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.30/1.76  tff(c_942, plain, (![A_228, B_229, D_230]: (r2_relset_1(A_228, B_229, D_230, D_230) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.76  tff(c_947, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_32, c_942])).
% 4.30/1.76  tff(c_800, plain, (![C_196, B_197, A_198]: (v5_relat_1(C_196, B_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.76  tff(c_808, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_800])).
% 4.30/1.76  tff(c_821, plain, (![B_205, A_206]: (k2_relat_1(B_205)=A_206 | ~v2_funct_2(B_205, A_206) | ~v5_relat_1(B_205, A_206) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.30/1.76  tff(c_827, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_808, c_821])).
% 4.30/1.76  tff(c_833, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_827])).
% 4.30/1.76  tff(c_834, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_833])).
% 4.30/1.76  tff(c_917, plain, (![C_225, B_226, A_227]: (v2_funct_2(C_225, B_226) | ~v3_funct_2(C_225, A_227, B_226) | ~v1_funct_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.76  tff(c_923, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_917])).
% 4.30/1.76  tff(c_927, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_923])).
% 4.30/1.76  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_927])).
% 4.30/1.76  tff(c_930, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_833])).
% 4.30/1.76  tff(c_38, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.30/1.76  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.76  tff(c_58, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 4.30/1.76  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.30/1.76  tff(c_951, plain, (![A_233, B_234, C_235]: (k2_relset_1(A_233, B_234, C_235)=k2_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.76  tff(c_957, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_951])).
% 4.30/1.76  tff(c_960, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_930, c_957])).
% 4.30/1.76  tff(c_1100, plain, (![C_260, A_261, B_262]: (v1_funct_1(k2_funct_1(C_260)) | k2_relset_1(A_261, B_262, C_260)!=B_262 | ~v2_funct_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(C_260, A_261, B_262) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.30/1.76  tff(c_1106, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1100])).
% 4.30/1.76  tff(c_1111, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1006, c_960, c_1106])).
% 4.30/1.76  tff(c_40, plain, (![C_35, B_34, A_33]: (m1_subset_1(k2_funct_1(C_35), k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~v2_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.30/1.76  tff(c_1196, plain, (![E_278, A_280, F_279, B_277, D_281, C_276]: (k1_partfun1(A_280, B_277, C_276, D_281, E_278, F_279)=k5_relat_1(E_278, F_279) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_276, D_281))) | ~v1_funct_1(F_279) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_277))) | ~v1_funct_1(E_278))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.76  tff(c_1202, plain, (![A_280, B_277, E_278]: (k1_partfun1(A_280, B_277, '#skF_1', '#skF_1', E_278, '#skF_2')=k5_relat_1(E_278, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_277))) | ~v1_funct_1(E_278))), inference(resolution, [status(thm)], [c_50, c_1196])).
% 4.30/1.76  tff(c_1208, plain, (![A_282, B_283, E_284]: (k1_partfun1(A_282, B_283, '#skF_1', '#skF_1', E_284, '#skF_2')=k5_relat_1(E_284, '#skF_2') | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(E_284))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1202])).
% 4.30/1.76  tff(c_1268, plain, (![B_296, A_297, C_298]: (k1_partfun1(B_296, A_297, '#skF_1', '#skF_1', k2_funct_1(C_298), '#skF_2')=k5_relat_1(k2_funct_1(C_298), '#skF_2') | ~v1_funct_1(k2_funct_1(C_298)) | k2_relset_1(A_297, B_296, C_298)!=B_296 | ~v2_funct_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))) | ~v1_funct_2(C_298, A_297, B_296) | ~v1_funct_1(C_298))), inference(resolution, [status(thm)], [c_40, c_1208])).
% 4.30/1.76  tff(c_1277, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1268])).
% 4.30/1.76  tff(c_1283, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1006, c_960, c_1111, c_1277])).
% 4.30/1.76  tff(c_1078, plain, (![A_258, B_259]: (k2_funct_2(A_258, B_259)=k2_funct_1(B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~v3_funct_2(B_259, A_258, A_258) | ~v1_funct_2(B_259, A_258, A_258) | ~v1_funct_1(B_259))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.76  tff(c_1084, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1078])).
% 4.30/1.76  tff(c_1088, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1084])).
% 4.30/1.76  tff(c_277, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.76  tff(c_283, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_277])).
% 4.30/1.76  tff(c_287, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_283])).
% 4.30/1.76  tff(c_223, plain, (![A_77, B_78, D_79]: (r2_relset_1(A_77, B_78, D_79, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.76  tff(c_228, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_32, c_223])).
% 4.30/1.76  tff(c_232, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.30/1.76  tff(c_240, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_232])).
% 4.30/1.76  tff(c_318, plain, (![A_99, B_100]: (k1_relset_1(A_99, A_99, B_100)=A_99 | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.30/1.76  tff(c_324, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_318])).
% 4.30/1.76  tff(c_329, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_240, c_324])).
% 4.30/1.76  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.76  tff(c_57, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 4.30/1.76  tff(c_81, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.76  tff(c_89, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_81])).
% 4.30/1.76  tff(c_102, plain, (![B_54, A_55]: (k2_relat_1(B_54)=A_55 | ~v2_funct_2(B_54, A_55) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.30/1.76  tff(c_108, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_89, c_102])).
% 4.30/1.76  tff(c_114, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_108])).
% 4.30/1.76  tff(c_115, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 4.30/1.76  tff(c_198, plain, (![C_74, B_75, A_76]: (v2_funct_2(C_74, B_75) | ~v3_funct_2(C_74, A_76, B_75) | ~v1_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.76  tff(c_204, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_198])).
% 4.30/1.76  tff(c_208, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_204])).
% 4.30/1.76  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_208])).
% 4.30/1.76  tff(c_211, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_114])).
% 4.30/1.76  tff(c_245, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.76  tff(c_251, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_245])).
% 4.30/1.76  tff(c_254, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_251])).
% 4.30/1.76  tff(c_371, plain, (![C_110, A_111, B_112]: (v1_funct_1(k2_funct_1(C_110)) | k2_relset_1(A_111, B_112, C_110)!=B_112 | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_110, A_111, B_112) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.30/1.76  tff(c_377, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_371])).
% 4.30/1.76  tff(c_382, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_287, c_254, c_377])).
% 4.30/1.76  tff(c_422, plain, (![C_128, B_129, A_130]: (m1_subset_1(k2_funct_1(C_128), k1_zfmisc_1(k2_zfmisc_1(B_129, A_130))) | k2_relset_1(A_130, B_129, C_128)!=B_129 | ~v2_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_128, A_130, B_129) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.30/1.76  tff(c_34, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29)=k5_relat_1(E_28, F_29) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.76  tff(c_758, plain, (![E_188, A_190, B_189, A_186, C_191, B_187]: (k1_partfun1(A_190, B_187, B_189, A_186, E_188, k2_funct_1(C_191))=k5_relat_1(E_188, k2_funct_1(C_191)) | ~v1_funct_1(k2_funct_1(C_191)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_190, B_187))) | ~v1_funct_1(E_188) | k2_relset_1(A_186, B_189, C_191)!=B_189 | ~v2_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_186, B_189))) | ~v1_funct_2(C_191, A_186, B_189) | ~v1_funct_1(C_191))), inference(resolution, [status(thm)], [c_422, c_34])).
% 4.30/1.76  tff(c_764, plain, (![B_189, A_186, C_191]: (k1_partfun1('#skF_1', '#skF_1', B_189, A_186, '#skF_2', k2_funct_1(C_191))=k5_relat_1('#skF_2', k2_funct_1(C_191)) | ~v1_funct_1(k2_funct_1(C_191)) | ~v1_funct_1('#skF_2') | k2_relset_1(A_186, B_189, C_191)!=B_189 | ~v2_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_186, B_189))) | ~v1_funct_2(C_191, A_186, B_189) | ~v1_funct_1(C_191))), inference(resolution, [status(thm)], [c_50, c_758])).
% 4.30/1.76  tff(c_770, plain, (![B_192, A_193, C_194]: (k1_partfun1('#skF_1', '#skF_1', B_192, A_193, '#skF_2', k2_funct_1(C_194))=k5_relat_1('#skF_2', k2_funct_1(C_194)) | ~v1_funct_1(k2_funct_1(C_194)) | k2_relset_1(A_193, B_192, C_194)!=B_192 | ~v2_funct_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))) | ~v1_funct_2(C_194, A_193, B_192) | ~v1_funct_1(C_194))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_764])).
% 4.30/1.76  tff(c_779, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_770])).
% 4.30/1.76  tff(c_785, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_287, c_254, c_382, c_779])).
% 4.30/1.76  tff(c_354, plain, (![A_107, B_108]: (k2_funct_2(A_107, B_108)=k2_funct_1(B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v3_funct_2(B_108, A_107, A_107) | ~v1_funct_2(B_108, A_107, A_107) | ~v1_funct_1(B_108))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.76  tff(c_360, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_354])).
% 4.30/1.76  tff(c_364, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_360])).
% 4.30/1.76  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.30/1.76  tff(c_79, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.30/1.76  tff(c_365, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_79])).
% 4.30/1.76  tff(c_786, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_365])).
% 4.30/1.76  tff(c_793, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_786])).
% 4.30/1.76  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_287, c_228, c_329, c_793])).
% 4.30/1.76  tff(c_797, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 4.30/1.76  tff(c_1089, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_797])).
% 4.30/1.76  tff(c_1284, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_1089])).
% 4.30/1.76  tff(c_1291, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1284])).
% 4.30/1.76  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_1006, c_947, c_930, c_1291])).
% 4.30/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.76  
% 4.30/1.76  Inference rules
% 4.30/1.76  ----------------------
% 4.30/1.76  #Ref     : 0
% 4.30/1.76  #Sup     : 265
% 4.30/1.76  #Fact    : 0
% 4.30/1.76  #Define  : 0
% 4.30/1.76  #Split   : 7
% 4.30/1.76  #Chain   : 0
% 4.30/1.76  #Close   : 0
% 4.30/1.76  
% 4.30/1.76  Ordering : KBO
% 4.30/1.76  
% 4.30/1.76  Simplification rules
% 4.30/1.76  ----------------------
% 4.30/1.76  #Subsume      : 6
% 4.30/1.76  #Demod        : 210
% 4.30/1.76  #Tautology    : 98
% 4.30/1.76  #SimpNegUnit  : 4
% 4.30/1.76  #BackRed      : 8
% 4.30/1.76  
% 4.30/1.76  #Partial instantiations: 0
% 4.30/1.76  #Strategies tried      : 1
% 4.30/1.76  
% 4.30/1.76  Timing (in seconds)
% 4.30/1.76  ----------------------
% 4.30/1.76  Preprocessing        : 0.37
% 4.30/1.76  Parsing              : 0.20
% 4.30/1.76  CNF conversion       : 0.02
% 4.30/1.76  Main loop            : 0.55
% 4.30/1.76  Inferencing          : 0.21
% 4.30/1.76  Reduction            : 0.17
% 4.30/1.76  Demodulation         : 0.12
% 4.30/1.76  BG Simplification    : 0.03
% 4.30/1.76  Subsumption          : 0.09
% 4.30/1.76  Abstraction          : 0.03
% 4.30/1.76  MUC search           : 0.00
% 4.30/1.76  Cooper               : 0.00
% 4.30/1.76  Total                : 0.97
% 4.30/1.76  Index Insertion      : 0.00
% 4.30/1.76  Index Deletion       : 0.00
% 4.30/1.76  Index Matching       : 0.00
% 4.30/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
