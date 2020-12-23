%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 389 expanded)
%              Number of leaves         :   42 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 (1114 expanded)
%              Number of equality atoms :   65 ( 112 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_142,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_105,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(f_83,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_103,axiom,(
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

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_983,plain,(
    ! [C_237,A_238,B_239] :
      ( v2_funct_1(C_237)
      | ~ v3_funct_2(C_237,A_238,B_239)
      | ~ v1_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_989,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_983])).

tff(c_993,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_989])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20])).

tff(c_939,plain,(
    ! [A_226,B_227,D_228] :
      ( r2_relset_1(A_226,B_227,D_228,D_228)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_944,plain,(
    ! [A_18] : r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18)) ),
    inference(resolution,[status(thm)],[c_55,c_939])).

tff(c_796,plain,(
    ! [C_193,B_194,A_195] :
      ( v5_relat_1(C_193,B_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_804,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_796])).

tff(c_817,plain,(
    ! [B_202,A_203] :
      ( k2_relat_1(B_202) = A_203
      | ~ v2_funct_2(B_202,A_203)
      | ~ v5_relat_1(B_202,A_203)
      | ~ v1_relat_1(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_823,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_804,c_817])).

tff(c_829,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_823])).

tff(c_830,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_829])).

tff(c_913,plain,(
    ! [C_222,B_223,A_224] :
      ( v2_funct_2(C_222,B_223)
      | ~ v3_funct_2(C_222,A_224,B_223)
      | ~ v1_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_919,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_913])).

tff(c_923,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_919])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_923])).

tff(c_926,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_829])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_956,plain,(
    ! [A_233,B_234,C_235] :
      ( k2_relset_1(A_233,B_234,C_235) = k2_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_962,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_956])).

tff(c_965,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_962])).

tff(c_1096,plain,(
    ! [C_257,A_258,B_259] :
      ( v1_funct_1(k2_funct_1(C_257))
      | k2_relset_1(A_258,B_259,C_257) != B_259
      | ~ v2_funct_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_257,A_258,B_259)
      | ~ v1_funct_1(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1102,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1096])).

tff(c_1107,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_993,c_965,c_1102])).

tff(c_38,plain,(
    ! [C_35,B_34,A_33] :
      ( m1_subset_1(k2_funct_1(C_35),k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ v2_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1191,plain,(
    ! [E_274,A_276,F_275,C_272,D_277,B_273] :
      ( k1_partfun1(A_276,B_273,C_272,D_277,E_274,F_275) = k5_relat_1(E_274,F_275)
      | ~ m1_subset_1(F_275,k1_zfmisc_1(k2_zfmisc_1(C_272,D_277)))
      | ~ v1_funct_1(F_275)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(A_276,B_273)))
      | ~ v1_funct_1(E_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1197,plain,(
    ! [A_276,B_273,E_274] :
      ( k1_partfun1(A_276,B_273,'#skF_1','#skF_1',E_274,'#skF_2') = k5_relat_1(E_274,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(A_276,B_273)))
      | ~ v1_funct_1(E_274) ) ),
    inference(resolution,[status(thm)],[c_48,c_1191])).

tff(c_1203,plain,(
    ! [A_278,B_279,E_280] :
      ( k1_partfun1(A_278,B_279,'#skF_1','#skF_1',E_280,'#skF_2') = k5_relat_1(E_280,'#skF_2')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1197])).

tff(c_1263,plain,(
    ! [B_289,A_290,C_291] :
      ( k1_partfun1(B_289,A_290,'#skF_1','#skF_1',k2_funct_1(C_291),'#skF_2') = k5_relat_1(k2_funct_1(C_291),'#skF_2')
      | ~ v1_funct_1(k2_funct_1(C_291))
      | k2_relset_1(A_290,B_289,C_291) != B_289
      | ~ v2_funct_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289)))
      | ~ v1_funct_2(C_291,A_290,B_289)
      | ~ v1_funct_1(C_291) ) ),
    inference(resolution,[status(thm)],[c_38,c_1203])).

tff(c_1272,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1263])).

tff(c_1278,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_993,c_965,c_1107,c_1272])).

tff(c_1074,plain,(
    ! [A_255,B_256] :
      ( k2_funct_2(A_255,B_256) = k2_funct_1(B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | ~ v3_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1080,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1074])).

tff(c_1084,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1080])).

tff(c_266,plain,(
    ! [C_88,A_89,B_90] :
      ( v2_funct_1(C_88)
      | ~ v3_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_272,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_266])).

tff(c_276,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_272])).

tff(c_222,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_relset_1(A_77,B_78,D_79,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_227,plain,(
    ! [A_18] : r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18)) ),
    inference(resolution,[status(thm)],[c_55,c_222])).

tff(c_240,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_248,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_240])).

tff(c_317,plain,(
    ! [A_99,B_100] :
      ( k1_relset_1(A_99,A_99,B_100) = A_99
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_323,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_317])).

tff(c_328,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_248,c_323])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_79,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_100,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(B_53) = A_54
      | ~ v2_funct_2(B_53,A_54)
      | ~ v5_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_100])).

tff(c_112,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_106])).

tff(c_113,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_196,plain,(
    ! [C_73,B_74,A_75] :
      ( v2_funct_2(C_73,B_74)
      | ~ v3_funct_2(C_73,A_75,B_74)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_202,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_196])).

tff(c_206,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_202])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_206])).

tff(c_209,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_230,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_236,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_239,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_236])).

tff(c_368,plain,(
    ! [C_108,A_109,B_110] :
      ( v1_funct_1(k2_funct_1(C_108))
      | k2_relset_1(A_109,B_110,C_108) != B_110
      | ~ v2_funct_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(C_108,A_109,B_110)
      | ~ v1_funct_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_374,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_368])).

tff(c_379,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_276,c_239,c_374])).

tff(c_419,plain,(
    ! [C_126,B_127,A_128] :
      ( m1_subset_1(k2_funct_1(C_126),k1_zfmisc_1(k2_zfmisc_1(B_127,A_128)))
      | k2_relset_1(A_128,B_127,C_126) != B_127
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_2(C_126,A_128,B_127)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29) = k5_relat_1(E_28,F_29)
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_755,plain,(
    ! [B_189,E_185,A_187,C_188,A_186,B_184] :
      ( k1_partfun1(A_187,B_184,B_189,A_186,E_185,k2_funct_1(C_188)) = k5_relat_1(E_185,k2_funct_1(C_188))
      | ~ v1_funct_1(k2_funct_1(C_188))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_187,B_184)))
      | ~ v1_funct_1(E_185)
      | k2_relset_1(A_186,B_189,C_188) != B_189
      | ~ v2_funct_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_189)))
      | ~ v1_funct_2(C_188,A_186,B_189)
      | ~ v1_funct_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_419,c_32])).

tff(c_761,plain,(
    ! [B_189,A_186,C_188] :
      ( k1_partfun1('#skF_1','#skF_1',B_189,A_186,'#skF_2',k2_funct_1(C_188)) = k5_relat_1('#skF_2',k2_funct_1(C_188))
      | ~ v1_funct_1(k2_funct_1(C_188))
      | ~ v1_funct_1('#skF_2')
      | k2_relset_1(A_186,B_189,C_188) != B_189
      | ~ v2_funct_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_189)))
      | ~ v1_funct_2(C_188,A_186,B_189)
      | ~ v1_funct_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_48,c_755])).

tff(c_767,plain,(
    ! [B_190,A_191,C_192] :
      ( k1_partfun1('#skF_1','#skF_1',B_190,A_191,'#skF_2',k2_funct_1(C_192)) = k5_relat_1('#skF_2',k2_funct_1(C_192))
      | ~ v1_funct_1(k2_funct_1(C_192))
      | k2_relset_1(A_191,B_190,C_192) != B_190
      | ~ v2_funct_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190)))
      | ~ v1_funct_2(C_192,A_191,B_190)
      | ~ v1_funct_1(C_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_761])).

tff(c_776,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_767])).

tff(c_782,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_276,c_239,c_379,c_776])).

tff(c_352,plain,(
    ! [A_106,B_107] :
      ( k2_funct_2(A_106,B_107) = k2_funct_1(B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v3_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_358,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_352])).

tff(c_362,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_358])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_363,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_78])).

tff(c_783,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_363])).

tff(c_790,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_783])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_276,c_227,c_328,c_790])).

tff(c_794,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1086,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_794])).

tff(c_1279,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1086])).

tff(c_1286,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1279])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_993,c_944,c_926,c_1286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.63  
% 4.01/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.63  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.01/1.63  
% 4.01/1.63  %Foreground sorts:
% 4.01/1.63  
% 4.01/1.63  
% 4.01/1.63  %Background operators:
% 4.01/1.63  
% 4.01/1.63  
% 4.01/1.63  %Foreground operators:
% 4.01/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.01/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.01/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.01/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.01/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.01/1.63  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.01/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.63  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.63  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.63  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.01/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.01/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.01/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.01/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.01/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.01/1.63  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.01/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.63  
% 4.01/1.66  tff(f_142, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 4.01/1.66  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.01/1.66  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.01/1.66  tff(f_105, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.01/1.66  tff(f_63, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.01/1.66  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.01/1.66  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.01/1.66  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.01/1.66  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.01/1.66  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.01/1.66  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.01/1.66  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.01/1.66  tff(f_103, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.01/1.66  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.01/1.66  tff(f_129, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 4.01/1.66  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.66  tff(c_68, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.01/1.66  tff(c_76, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 4.01/1.66  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.66  tff(c_50, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.66  tff(c_983, plain, (![C_237, A_238, B_239]: (v2_funct_1(C_237) | ~v3_funct_2(C_237, A_238, B_239) | ~v1_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.66  tff(c_989, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_983])).
% 4.01/1.66  tff(c_993, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_989])).
% 4.01/1.66  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.66  tff(c_20, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.01/1.66  tff(c_55, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20])).
% 4.01/1.66  tff(c_939, plain, (![A_226, B_227, D_228]: (r2_relset_1(A_226, B_227, D_228, D_228) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.66  tff(c_944, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)))), inference(resolution, [status(thm)], [c_55, c_939])).
% 4.01/1.66  tff(c_796, plain, (![C_193, B_194, A_195]: (v5_relat_1(C_193, B_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.66  tff(c_804, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_796])).
% 4.01/1.66  tff(c_817, plain, (![B_202, A_203]: (k2_relat_1(B_202)=A_203 | ~v2_funct_2(B_202, A_203) | ~v5_relat_1(B_202, A_203) | ~v1_relat_1(B_202))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.66  tff(c_823, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_804, c_817])).
% 4.01/1.66  tff(c_829, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_823])).
% 4.01/1.66  tff(c_830, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_829])).
% 4.01/1.66  tff(c_913, plain, (![C_222, B_223, A_224]: (v2_funct_2(C_222, B_223) | ~v3_funct_2(C_222, A_224, B_223) | ~v1_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.66  tff(c_919, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_913])).
% 4.01/1.66  tff(c_923, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_919])).
% 4.01/1.66  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_923])).
% 4.01/1.66  tff(c_926, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_829])).
% 4.01/1.66  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.66  tff(c_57, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 4.01/1.66  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.66  tff(c_956, plain, (![A_233, B_234, C_235]: (k2_relset_1(A_233, B_234, C_235)=k2_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.66  tff(c_962, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_956])).
% 4.01/1.66  tff(c_965, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_926, c_962])).
% 4.01/1.66  tff(c_1096, plain, (![C_257, A_258, B_259]: (v1_funct_1(k2_funct_1(C_257)) | k2_relset_1(A_258, B_259, C_257)!=B_259 | ~v2_funct_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_257, A_258, B_259) | ~v1_funct_1(C_257))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.01/1.66  tff(c_1102, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1096])).
% 4.01/1.66  tff(c_1107, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_993, c_965, c_1102])).
% 4.01/1.66  tff(c_38, plain, (![C_35, B_34, A_33]: (m1_subset_1(k2_funct_1(C_35), k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~v2_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.01/1.66  tff(c_1191, plain, (![E_274, A_276, F_275, C_272, D_277, B_273]: (k1_partfun1(A_276, B_273, C_272, D_277, E_274, F_275)=k5_relat_1(E_274, F_275) | ~m1_subset_1(F_275, k1_zfmisc_1(k2_zfmisc_1(C_272, D_277))) | ~v1_funct_1(F_275) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(A_276, B_273))) | ~v1_funct_1(E_274))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.66  tff(c_1197, plain, (![A_276, B_273, E_274]: (k1_partfun1(A_276, B_273, '#skF_1', '#skF_1', E_274, '#skF_2')=k5_relat_1(E_274, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(A_276, B_273))) | ~v1_funct_1(E_274))), inference(resolution, [status(thm)], [c_48, c_1191])).
% 4.01/1.66  tff(c_1203, plain, (![A_278, B_279, E_280]: (k1_partfun1(A_278, B_279, '#skF_1', '#skF_1', E_280, '#skF_2')=k5_relat_1(E_280, '#skF_2') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_1(E_280))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1197])).
% 4.01/1.66  tff(c_1263, plain, (![B_289, A_290, C_291]: (k1_partfun1(B_289, A_290, '#skF_1', '#skF_1', k2_funct_1(C_291), '#skF_2')=k5_relat_1(k2_funct_1(C_291), '#skF_2') | ~v1_funct_1(k2_funct_1(C_291)) | k2_relset_1(A_290, B_289, C_291)!=B_289 | ~v2_funct_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))) | ~v1_funct_2(C_291, A_290, B_289) | ~v1_funct_1(C_291))), inference(resolution, [status(thm)], [c_38, c_1203])).
% 4.01/1.66  tff(c_1272, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1263])).
% 4.01/1.66  tff(c_1278, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_993, c_965, c_1107, c_1272])).
% 4.01/1.66  tff(c_1074, plain, (![A_255, B_256]: (k2_funct_2(A_255, B_256)=k2_funct_1(B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | ~v3_funct_2(B_256, A_255, A_255) | ~v1_funct_2(B_256, A_255, A_255) | ~v1_funct_1(B_256))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.66  tff(c_1080, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1074])).
% 4.01/1.66  tff(c_1084, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1080])).
% 4.01/1.66  tff(c_266, plain, (![C_88, A_89, B_90]: (v2_funct_1(C_88) | ~v3_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.66  tff(c_272, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_266])).
% 4.01/1.66  tff(c_276, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_272])).
% 4.01/1.66  tff(c_222, plain, (![A_77, B_78, D_79]: (r2_relset_1(A_77, B_78, D_79, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.66  tff(c_227, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)))), inference(resolution, [status(thm)], [c_55, c_222])).
% 4.01/1.66  tff(c_240, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.01/1.66  tff(c_248, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_240])).
% 4.01/1.66  tff(c_317, plain, (![A_99, B_100]: (k1_relset_1(A_99, A_99, B_100)=A_99 | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.66  tff(c_323, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_317])).
% 4.01/1.66  tff(c_328, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_248, c_323])).
% 4.01/1.66  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.66  tff(c_56, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 4.01/1.66  tff(c_79, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.66  tff(c_87, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_79])).
% 4.01/1.66  tff(c_100, plain, (![B_53, A_54]: (k2_relat_1(B_53)=A_54 | ~v2_funct_2(B_53, A_54) | ~v5_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.66  tff(c_106, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_87, c_100])).
% 4.01/1.66  tff(c_112, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_106])).
% 4.01/1.66  tff(c_113, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_112])).
% 4.01/1.66  tff(c_196, plain, (![C_73, B_74, A_75]: (v2_funct_2(C_73, B_74) | ~v3_funct_2(C_73, A_75, B_74) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.66  tff(c_202, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_196])).
% 4.01/1.66  tff(c_206, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_202])).
% 4.01/1.66  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_206])).
% 4.01/1.66  tff(c_209, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_112])).
% 4.01/1.66  tff(c_230, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.66  tff(c_236, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_230])).
% 4.01/1.66  tff(c_239, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_236])).
% 4.01/1.66  tff(c_368, plain, (![C_108, A_109, B_110]: (v1_funct_1(k2_funct_1(C_108)) | k2_relset_1(A_109, B_110, C_108)!=B_110 | ~v2_funct_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(C_108, A_109, B_110) | ~v1_funct_1(C_108))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.01/1.66  tff(c_374, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_368])).
% 4.01/1.66  tff(c_379, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_276, c_239, c_374])).
% 4.01/1.66  tff(c_419, plain, (![C_126, B_127, A_128]: (m1_subset_1(k2_funct_1(C_126), k1_zfmisc_1(k2_zfmisc_1(B_127, A_128))) | k2_relset_1(A_128, B_127, C_126)!=B_127 | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_2(C_126, A_128, B_127) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.01/1.66  tff(c_32, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29)=k5_relat_1(E_28, F_29) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.66  tff(c_755, plain, (![B_189, E_185, A_187, C_188, A_186, B_184]: (k1_partfun1(A_187, B_184, B_189, A_186, E_185, k2_funct_1(C_188))=k5_relat_1(E_185, k2_funct_1(C_188)) | ~v1_funct_1(k2_funct_1(C_188)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_187, B_184))) | ~v1_funct_1(E_185) | k2_relset_1(A_186, B_189, C_188)!=B_189 | ~v2_funct_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_189))) | ~v1_funct_2(C_188, A_186, B_189) | ~v1_funct_1(C_188))), inference(resolution, [status(thm)], [c_419, c_32])).
% 4.01/1.66  tff(c_761, plain, (![B_189, A_186, C_188]: (k1_partfun1('#skF_1', '#skF_1', B_189, A_186, '#skF_2', k2_funct_1(C_188))=k5_relat_1('#skF_2', k2_funct_1(C_188)) | ~v1_funct_1(k2_funct_1(C_188)) | ~v1_funct_1('#skF_2') | k2_relset_1(A_186, B_189, C_188)!=B_189 | ~v2_funct_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_189))) | ~v1_funct_2(C_188, A_186, B_189) | ~v1_funct_1(C_188))), inference(resolution, [status(thm)], [c_48, c_755])).
% 4.01/1.66  tff(c_767, plain, (![B_190, A_191, C_192]: (k1_partfun1('#skF_1', '#skF_1', B_190, A_191, '#skF_2', k2_funct_1(C_192))=k5_relat_1('#skF_2', k2_funct_1(C_192)) | ~v1_funct_1(k2_funct_1(C_192)) | k2_relset_1(A_191, B_190, C_192)!=B_190 | ~v2_funct_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))) | ~v1_funct_2(C_192, A_191, B_190) | ~v1_funct_1(C_192))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_761])).
% 4.01/1.66  tff(c_776, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_767])).
% 4.01/1.66  tff(c_782, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_276, c_239, c_379, c_776])).
% 4.01/1.66  tff(c_352, plain, (![A_106, B_107]: (k2_funct_2(A_106, B_107)=k2_funct_1(B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v3_funct_2(B_107, A_106, A_106) | ~v1_funct_2(B_107, A_106, A_106) | ~v1_funct_1(B_107))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.66  tff(c_358, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_352])).
% 4.01/1.66  tff(c_362, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_358])).
% 4.01/1.66  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.66  tff(c_78, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.01/1.66  tff(c_363, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_78])).
% 4.01/1.66  tff(c_783, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_363])).
% 4.01/1.66  tff(c_790, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_783])).
% 4.01/1.66  tff(c_793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_276, c_227, c_328, c_790])).
% 4.01/1.66  tff(c_794, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 4.01/1.66  tff(c_1086, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_794])).
% 4.01/1.66  tff(c_1279, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1086])).
% 4.01/1.66  tff(c_1286, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1279])).
% 4.01/1.66  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_993, c_944, c_926, c_1286])).
% 4.01/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.66  
% 4.01/1.66  Inference rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Ref     : 0
% 4.01/1.66  #Sup     : 265
% 4.01/1.66  #Fact    : 0
% 4.01/1.66  #Define  : 0
% 4.01/1.66  #Split   : 7
% 4.01/1.66  #Chain   : 0
% 4.01/1.66  #Close   : 0
% 4.01/1.66  
% 4.01/1.66  Ordering : KBO
% 4.01/1.66  
% 4.01/1.66  Simplification rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Subsume      : 6
% 4.01/1.66  #Demod        : 211
% 4.01/1.66  #Tautology    : 98
% 4.01/1.66  #SimpNegUnit  : 4
% 4.01/1.66  #BackRed      : 8
% 4.01/1.66  
% 4.01/1.66  #Partial instantiations: 0
% 4.01/1.66  #Strategies tried      : 1
% 4.01/1.66  
% 4.01/1.66  Timing (in seconds)
% 4.01/1.66  ----------------------
% 4.01/1.66  Preprocessing        : 0.35
% 4.01/1.66  Parsing              : 0.19
% 4.01/1.66  CNF conversion       : 0.02
% 4.01/1.66  Main loop            : 0.52
% 4.01/1.66  Inferencing          : 0.20
% 4.01/1.66  Reduction            : 0.16
% 4.01/1.66  Demodulation         : 0.11
% 4.01/1.66  BG Simplification    : 0.03
% 4.01/1.66  Subsumption          : 0.09
% 4.01/1.66  Abstraction          : 0.03
% 4.01/1.66  MUC search           : 0.00
% 4.01/1.66  Cooper               : 0.00
% 4.01/1.66  Total                : 0.92
% 4.01/1.66  Index Insertion      : 0.00
% 4.01/1.66  Index Deletion       : 0.00
% 4.01/1.66  Index Matching       : 0.00
% 4.01/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
