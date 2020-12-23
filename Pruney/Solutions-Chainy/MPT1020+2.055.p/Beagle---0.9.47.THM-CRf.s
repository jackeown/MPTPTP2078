%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  171 (3671 expanded)
%              Number of leaves         :   38 (1211 expanded)
%              Depth                    :   19
%              Number of atoms          :  339 (10499 expanded)
%              Number of equality atoms :   75 (1739 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_153,negated_conjecture,(
    ~ ! [A,B] :
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_96,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_72,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_326,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_relset_1(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_332,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_326])).

tff(c_101,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_101])).

tff(c_126,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(B_49) = A_50
      | ~ v2_funct_2(B_49,A_50)
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_129,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_126])).

tff(c_135,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_129])).

tff(c_139,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_234,plain,(
    ! [C_69,B_70,A_71] :
      ( v2_funct_2(C_69,B_70)
      | ~ v3_funct_2(C_69,A_71,B_70)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_240,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_234])).

tff(c_246,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_240])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_246])).

tff(c_249,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_110,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_251,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_110])).

tff(c_60,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_75,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_81,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_108,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_132,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_126])).

tff(c_138,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_132])).

tff(c_261,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_56,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_301,plain,(
    ! [C_81,B_82,A_83] :
      ( v2_funct_2(C_81,B_82)
      | ~ v3_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_304,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_301])).

tff(c_310,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_304])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_310])).

tff(c_313,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_334,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_337,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_334])).

tff(c_342,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_337])).

tff(c_353,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_356,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_353])).

tff(c_362,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_356])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_510,plain,(
    ! [C_110,D_111,B_112,A_113] :
      ( k2_funct_1(C_110) = D_111
      | k1_xboole_0 = B_112
      | k1_xboole_0 = A_113
      | ~ v2_funct_1(C_110)
      | ~ r2_relset_1(A_113,A_113,k1_partfun1(A_113,B_112,B_112,A_113,C_110,D_111),k6_partfun1(A_113))
      | k2_relset_1(A_113,B_112,C_110) != B_112
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(B_112,A_113)))
      | ~ v1_funct_2(D_111,B_112,A_113)
      | ~ v1_funct_1(D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_2(C_110,A_113,B_112)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_513,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_510])).

tff(c_516,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_46,c_342,c_362,c_513])).

tff(c_517,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_516])).

tff(c_409,plain,(
    ! [A_102,B_103] :
      ( k2_funct_2(A_102,B_103) = k2_funct_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_412,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_409])).

tff(c_418,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_412])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_423,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_42])).

tff(c_519,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_423])).

tff(c_526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_519])).

tff(c_527,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_528,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_535,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_528])).

tff(c_1145,plain,(
    ! [B_212,A_213] :
      ( k2_relat_1(B_212) = A_213
      | ~ v2_funct_2(B_212,A_213)
      | ~ v5_relat_1(B_212,A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1148,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_1145])).

tff(c_1151,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_535,c_1148])).

tff(c_1152,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1151])).

tff(c_1175,plain,(
    ! [C_223,B_224,A_225] :
      ( v2_funct_2(C_223,B_224)
      | ~ v3_funct_2(C_223,A_225,B_224)
      | ~ v1_funct_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1178,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1175])).

tff(c_1181,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1178])).

tff(c_1183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1152,c_1181])).

tff(c_1184,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1151])).

tff(c_1198,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_46])).

tff(c_16,plain,(
    ! [A_13,B_14,D_16] :
      ( r2_relset_1(A_13,B_14,D_16,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1242,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1198,c_16])).

tff(c_1201,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_52])).

tff(c_1200,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_50])).

tff(c_1199,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_48])).

tff(c_1319,plain,(
    ! [A_250,B_251] :
      ( k2_funct_2(A_250,B_251) = k2_funct_1(B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_zfmisc_1(A_250,A_250)))
      | ~ v3_funct_2(B_251,A_250,A_250)
      | ~ v1_funct_2(B_251,A_250,A_250)
      | ~ v1_funct_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1322,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1198,c_1319])).

tff(c_1325,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_1200,c_1199,c_1322])).

tff(c_1344,plain,(
    ! [A_256,B_257] :
      ( m1_subset_1(k2_funct_2(A_256,B_257),k1_zfmisc_1(k2_zfmisc_1(A_256,A_256)))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_zfmisc_1(A_256,A_256)))
      | ~ v3_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1377,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_1344])).

tff(c_1392,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_1200,c_1199,c_1198,c_1377])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1422,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1392,c_2])).

tff(c_1447,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1422])).

tff(c_529,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != '#skF_3'
      | A_6 = '#skF_3'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_6])).

tff(c_1192,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != '#skF_1'
      | A_6 = '#skF_1'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1184,c_529])).

tff(c_1456,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1447,c_1192])).

tff(c_1490,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1456])).

tff(c_1312,plain,(
    ! [A_248,B_249] :
      ( v1_funct_1(k2_funct_2(A_248,B_249))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248)))
      | ~ v3_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1315,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1198,c_1312])).

tff(c_1318,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_1200,c_1199,c_1315])).

tff(c_1326,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1318])).

tff(c_1332,plain,(
    ! [A_252,B_253] :
      ( v3_funct_2(k2_funct_2(A_252,B_253),A_252,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_zfmisc_1(A_252,A_252)))
      | ~ v3_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1334,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1198,c_1332])).

tff(c_1337,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_1200,c_1199,c_1325,c_1334])).

tff(c_20,plain,(
    ! [C_19,B_18,A_17] :
      ( v2_funct_2(C_19,B_18)
      | ~ v3_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1405,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1392,c_20])).

tff(c_1437,plain,(
    v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1337,c_1405])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( v5_relat_1(C_9,B_8)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1444,plain,(
    v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1392,c_10])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(B_21) = A_20
      | ~ v2_funct_2(B_21,A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1459,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1444,c_28])).

tff(c_1462,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_1459])).

tff(c_1522,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1462])).

tff(c_1523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1490,c_1522])).

tff(c_1524,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_797,plain,(
    ! [B_158,A_159] :
      ( k2_relat_1(B_158) = A_159
      | ~ v2_funct_2(B_158,A_159)
      | ~ v5_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_803,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_797])).

tff(c_812,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_535,c_803])).

tff(c_816,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_920,plain,(
    ! [C_181,B_182,A_183] :
      ( v2_funct_2(C_181,B_182)
      | ~ v3_funct_2(C_181,A_183,B_182)
      | ~ v1_funct_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_926,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_920])).

tff(c_932,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_926])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_816,c_932])).

tff(c_935,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_91,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_540,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_91])).

tff(c_541,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_945,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_541])).

tff(c_806,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_797])).

tff(c_815,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_806])).

tff(c_1005,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_945,c_815])).

tff(c_1070,plain,(
    ! [C_199,B_200,A_201] :
      ( v2_funct_2(C_199,B_200)
      | ~ v3_funct_2(C_199,A_201,B_200)
      | ~ v1_funct_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1076,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1070])).

tff(c_1082,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1076])).

tff(c_1084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_1082])).

tff(c_1085,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_1090,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_42])).

tff(c_1189,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1184,c_1090])).

tff(c_1327,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1189])).

tff(c_1539,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_1327])).

tff(c_1556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.59  
% 3.82/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.59  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.82/1.59  
% 3.82/1.59  %Foreground sorts:
% 3.82/1.59  
% 3.82/1.59  
% 3.82/1.59  %Background operators:
% 3.82/1.59  
% 3.82/1.59  
% 3.82/1.59  %Foreground operators:
% 3.82/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.82/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.82/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.82/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.82/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.59  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.82/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.82/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.82/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.59  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.82/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.82/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.82/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.82/1.59  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.82/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.59  
% 3.82/1.62  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.82/1.62  tff(f_153, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 3.82/1.62  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.82/1.62  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.82/1.62  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.82/1.62  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.82/1.62  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.82/1.62  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.82/1.62  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.82/1.62  tff(f_131, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.82/1.62  tff(f_106, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.82/1.62  tff(f_96, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.82/1.62  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.62  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_72, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.82/1.62  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_72])).
% 3.82/1.62  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_78])).
% 3.82/1.62  tff(c_326, plain, (![A_84, B_85, D_86]: (r2_relset_1(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.62  tff(c_332, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_326])).
% 3.82/1.62  tff(c_101, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.82/1.62  tff(c_109, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_101])).
% 3.82/1.62  tff(c_126, plain, (![B_49, A_50]: (k2_relat_1(B_49)=A_50 | ~v2_funct_2(B_49, A_50) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.82/1.62  tff(c_129, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_126])).
% 3.82/1.62  tff(c_135, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_129])).
% 3.82/1.62  tff(c_139, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_135])).
% 3.82/1.62  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_48, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_234, plain, (![C_69, B_70, A_71]: (v2_funct_2(C_69, B_70) | ~v3_funct_2(C_69, A_71, B_70) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_240, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_234])).
% 3.82/1.62  tff(c_246, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_240])).
% 3.82/1.62  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_246])).
% 3.82/1.62  tff(c_249, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_135])).
% 3.82/1.62  tff(c_6, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.62  tff(c_99, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_84, c_6])).
% 3.82/1.62  tff(c_110, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 3.82/1.62  tff(c_251, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_110])).
% 3.82/1.62  tff(c_60, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_58, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_75, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_72])).
% 3.82/1.62  tff(c_81, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_75])).
% 3.82/1.62  tff(c_108, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_101])).
% 3.82/1.62  tff(c_132, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_108, c_126])).
% 3.82/1.62  tff(c_138, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_132])).
% 3.82/1.62  tff(c_261, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_138])).
% 3.82/1.62  tff(c_56, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_301, plain, (![C_81, B_82, A_83]: (v2_funct_2(C_81, B_82) | ~v3_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_304, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_301])).
% 3.82/1.62  tff(c_310, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_304])).
% 3.82/1.62  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_310])).
% 3.82/1.62  tff(c_313, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_138])).
% 3.82/1.62  tff(c_334, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.62  tff(c_337, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_334])).
% 3.82/1.62  tff(c_342, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_337])).
% 3.82/1.62  tff(c_353, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_356, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_353])).
% 3.82/1.62  tff(c_362, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_356])).
% 3.82/1.62  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_510, plain, (![C_110, D_111, B_112, A_113]: (k2_funct_1(C_110)=D_111 | k1_xboole_0=B_112 | k1_xboole_0=A_113 | ~v2_funct_1(C_110) | ~r2_relset_1(A_113, A_113, k1_partfun1(A_113, B_112, B_112, A_113, C_110, D_111), k6_partfun1(A_113)) | k2_relset_1(A_113, B_112, C_110)!=B_112 | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(B_112, A_113))) | ~v1_funct_2(D_111, B_112, A_113) | ~v1_funct_1(D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_2(C_110, A_113, B_112) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.82/1.62  tff(c_513, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_510])).
% 3.82/1.62  tff(c_516, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_46, c_342, c_362, c_513])).
% 3.82/1.62  tff(c_517, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_251, c_516])).
% 3.82/1.62  tff(c_409, plain, (![A_102, B_103]: (k2_funct_2(A_102, B_103)=k2_funct_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.82/1.62  tff(c_412, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_409])).
% 3.82/1.62  tff(c_418, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_412])).
% 3.82/1.62  tff(c_42, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.82/1.62  tff(c_423, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_42])).
% 3.82/1.62  tff(c_519, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_423])).
% 3.82/1.62  tff(c_526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_519])).
% 3.82/1.62  tff(c_527, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_99])).
% 3.82/1.62  tff(c_528, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 3.82/1.62  tff(c_535, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_528])).
% 3.82/1.62  tff(c_1145, plain, (![B_212, A_213]: (k2_relat_1(B_212)=A_213 | ~v2_funct_2(B_212, A_213) | ~v5_relat_1(B_212, A_213) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.82/1.62  tff(c_1148, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_1145])).
% 3.82/1.62  tff(c_1151, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_535, c_1148])).
% 3.82/1.62  tff(c_1152, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1151])).
% 3.82/1.62  tff(c_1175, plain, (![C_223, B_224, A_225]: (v2_funct_2(C_223, B_224) | ~v3_funct_2(C_223, A_225, B_224) | ~v1_funct_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_1178, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1175])).
% 3.82/1.62  tff(c_1181, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1178])).
% 3.82/1.62  tff(c_1183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1152, c_1181])).
% 3.82/1.62  tff(c_1184, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1151])).
% 3.82/1.62  tff(c_1198, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_46])).
% 3.82/1.62  tff(c_16, plain, (![A_13, B_14, D_16]: (r2_relset_1(A_13, B_14, D_16, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.62  tff(c_1242, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1198, c_16])).
% 3.82/1.62  tff(c_1201, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_52])).
% 3.82/1.62  tff(c_1200, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_50])).
% 3.82/1.62  tff(c_1199, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_48])).
% 3.82/1.62  tff(c_1319, plain, (![A_250, B_251]: (k2_funct_2(A_250, B_251)=k2_funct_1(B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(k2_zfmisc_1(A_250, A_250))) | ~v3_funct_2(B_251, A_250, A_250) | ~v1_funct_2(B_251, A_250, A_250) | ~v1_funct_1(B_251))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.82/1.62  tff(c_1322, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1198, c_1319])).
% 3.82/1.62  tff(c_1325, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_1200, c_1199, c_1322])).
% 3.82/1.62  tff(c_1344, plain, (![A_256, B_257]: (m1_subset_1(k2_funct_2(A_256, B_257), k1_zfmisc_1(k2_zfmisc_1(A_256, A_256))) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_zfmisc_1(A_256, A_256))) | ~v3_funct_2(B_257, A_256, A_256) | ~v1_funct_2(B_257, A_256, A_256) | ~v1_funct_1(B_257))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.82/1.62  tff(c_1377, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1325, c_1344])).
% 3.82/1.62  tff(c_1392, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_1200, c_1199, c_1198, c_1377])).
% 3.82/1.62  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.82/1.62  tff(c_1422, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1392, c_2])).
% 3.82/1.62  tff(c_1447, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1422])).
% 3.82/1.62  tff(c_529, plain, (![A_6]: (k2_relat_1(A_6)!='#skF_3' | A_6='#skF_3' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_6])).
% 3.82/1.62  tff(c_1192, plain, (![A_6]: (k2_relat_1(A_6)!='#skF_1' | A_6='#skF_1' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1184, c_529])).
% 3.82/1.62  tff(c_1456, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1447, c_1192])).
% 3.82/1.62  tff(c_1490, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_1456])).
% 3.82/1.62  tff(c_1312, plain, (![A_248, B_249]: (v1_funct_1(k2_funct_2(A_248, B_249)) | ~m1_subset_1(B_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))) | ~v3_funct_2(B_249, A_248, A_248) | ~v1_funct_2(B_249, A_248, A_248) | ~v1_funct_1(B_249))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.82/1.62  tff(c_1315, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1198, c_1312])).
% 3.82/1.62  tff(c_1318, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_1200, c_1199, c_1315])).
% 3.82/1.62  tff(c_1326, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1318])).
% 3.82/1.62  tff(c_1332, plain, (![A_252, B_253]: (v3_funct_2(k2_funct_2(A_252, B_253), A_252, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(k2_zfmisc_1(A_252, A_252))) | ~v3_funct_2(B_253, A_252, A_252) | ~v1_funct_2(B_253, A_252, A_252) | ~v1_funct_1(B_253))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.82/1.62  tff(c_1334, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1198, c_1332])).
% 3.82/1.62  tff(c_1337, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_1200, c_1199, c_1325, c_1334])).
% 3.82/1.62  tff(c_20, plain, (![C_19, B_18, A_17]: (v2_funct_2(C_19, B_18) | ~v3_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_1405, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1392, c_20])).
% 3.82/1.62  tff(c_1437, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1337, c_1405])).
% 3.82/1.62  tff(c_10, plain, (![C_9, B_8, A_7]: (v5_relat_1(C_9, B_8) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.82/1.62  tff(c_1444, plain, (v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_1392, c_10])).
% 3.82/1.62  tff(c_28, plain, (![B_21, A_20]: (k2_relat_1(B_21)=A_20 | ~v2_funct_2(B_21, A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.82/1.62  tff(c_1459, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1444, c_28])).
% 3.82/1.62  tff(c_1462, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_1459])).
% 3.82/1.62  tff(c_1522, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1462])).
% 3.82/1.62  tff(c_1523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1490, c_1522])).
% 3.82/1.62  tff(c_1524, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_1456])).
% 3.82/1.62  tff(c_797, plain, (![B_158, A_159]: (k2_relat_1(B_158)=A_159 | ~v2_funct_2(B_158, A_159) | ~v5_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.82/1.62  tff(c_803, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_797])).
% 3.82/1.62  tff(c_812, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_535, c_803])).
% 3.82/1.62  tff(c_816, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_812])).
% 3.82/1.62  tff(c_920, plain, (![C_181, B_182, A_183]: (v2_funct_2(C_181, B_182) | ~v3_funct_2(C_181, A_183, B_182) | ~v1_funct_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_926, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_920])).
% 3.82/1.62  tff(c_932, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_926])).
% 3.82/1.62  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_816, c_932])).
% 3.82/1.62  tff(c_935, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_812])).
% 3.82/1.62  tff(c_91, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_81, c_6])).
% 3.82/1.62  tff(c_540, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_91])).
% 3.82/1.62  tff(c_541, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_540])).
% 3.82/1.62  tff(c_945, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_541])).
% 3.82/1.62  tff(c_806, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_108, c_797])).
% 3.82/1.62  tff(c_815, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_806])).
% 3.82/1.62  tff(c_1005, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_945, c_815])).
% 3.82/1.62  tff(c_1070, plain, (![C_199, B_200, A_201]: (v2_funct_2(C_199, B_200) | ~v3_funct_2(C_199, A_201, B_200) | ~v1_funct_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.62  tff(c_1076, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1070])).
% 3.82/1.62  tff(c_1082, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1076])).
% 3.82/1.62  tff(c_1084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1005, c_1082])).
% 3.82/1.62  tff(c_1085, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_540])).
% 3.82/1.62  tff(c_1090, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_42])).
% 3.82/1.62  tff(c_1189, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1184, c_1090])).
% 3.82/1.62  tff(c_1327, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1189])).
% 3.82/1.62  tff(c_1539, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_1327])).
% 3.82/1.62  tff(c_1556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1539])).
% 3.82/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.62  
% 3.82/1.62  Inference rules
% 3.82/1.62  ----------------------
% 3.82/1.62  #Ref     : 0
% 3.82/1.62  #Sup     : 295
% 3.82/1.62  #Fact    : 0
% 3.82/1.62  #Define  : 0
% 3.82/1.62  #Split   : 20
% 3.82/1.62  #Chain   : 0
% 3.82/1.62  #Close   : 0
% 3.82/1.62  
% 3.82/1.62  Ordering : KBO
% 3.82/1.62  
% 3.82/1.62  Simplification rules
% 3.82/1.62  ----------------------
% 3.82/1.62  #Subsume      : 19
% 3.82/1.62  #Demod        : 456
% 3.82/1.62  #Tautology    : 154
% 3.82/1.62  #SimpNegUnit  : 12
% 3.82/1.62  #BackRed      : 97
% 3.82/1.62  
% 3.82/1.62  #Partial instantiations: 0
% 3.82/1.62  #Strategies tried      : 1
% 3.82/1.62  
% 3.82/1.62  Timing (in seconds)
% 3.82/1.62  ----------------------
% 3.82/1.62  Preprocessing        : 0.34
% 3.82/1.62  Parsing              : 0.18
% 3.82/1.62  CNF conversion       : 0.02
% 3.82/1.62  Main loop            : 0.50
% 3.82/1.62  Inferencing          : 0.18
% 3.82/1.62  Reduction            : 0.17
% 3.82/1.62  Demodulation         : 0.12
% 3.82/1.62  BG Simplification    : 0.02
% 3.82/1.62  Subsumption          : 0.07
% 3.82/1.62  Abstraction          : 0.02
% 3.82/1.62  MUC search           : 0.00
% 3.82/1.62  Cooper               : 0.00
% 3.82/1.62  Total                : 0.89
% 3.82/1.62  Index Insertion      : 0.00
% 3.82/1.62  Index Deletion       : 0.00
% 3.82/1.62  Index Matching       : 0.00
% 3.82/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
