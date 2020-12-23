%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 234 expanded)
%              Number of leaves         :   40 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 718 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_93,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_73,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_86,plain,(
    ! [A_48] :
      ( v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_71,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_89,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_71])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_89])).

tff(c_121,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_xboole_0(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_130])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_260,plain,(
    ! [D_92,E_90,F_89,B_91,A_93,C_88] :
      ( m1_subset_1(k1_partfun1(A_93,B_91,C_88,D_92,E_90,F_89),k1_zfmisc_1(k2_zfmisc_1(A_93,D_92)))
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_88,D_92)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_190,plain,(
    ! [D_73,C_74,A_75,B_76] :
      ( D_73 = C_74
      | ~ r2_relset_1(A_75,B_76,C_74,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_190])).

tff(c_213,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_198])).

tff(c_227,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_268,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_260,c_227])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_268])).

tff(c_292,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_497,plain,(
    ! [E_151,D_150,B_152,A_148,C_149] :
      ( k1_xboole_0 = C_149
      | v2_funct_1(D_150)
      | ~ v2_funct_1(k1_partfun1(A_148,B_152,B_152,C_149,D_150,E_151))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(B_152,C_149)))
      | ~ v1_funct_2(E_151,B_152,C_149)
      | ~ v1_funct_1(E_151)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_152)))
      | ~ v1_funct_2(D_150,A_148,B_152)
      | ~ v1_funct_1(D_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_499,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_497])).

tff(c_504,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_60,c_499])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_504])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_509,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_2])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_509])).

tff(c_512,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_515,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_526,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_515])).

tff(c_544,plain,(
    ! [C_163,B_164,A_165] :
      ( v5_relat_1(C_163,B_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_555,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_544])).

tff(c_575,plain,(
    ! [A_172,B_173,D_174] :
      ( r2_relset_1(A_172,B_173,D_174,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_582,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_59,c_575])).

tff(c_605,plain,(
    ! [A_177,B_178,C_179] :
      ( k2_relset_1(A_177,B_178,C_179) = k2_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_616,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_605])).

tff(c_711,plain,(
    ! [C_200,D_204,B_203,A_205,F_201,E_202] :
      ( m1_subset_1(k1_partfun1(A_205,B_203,C_200,D_204,E_202,F_201),k1_zfmisc_1(k2_zfmisc_1(A_205,D_204)))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_200,D_204)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_205,B_203)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_637,plain,(
    ! [D_183,C_184,A_185,B_186] :
      ( D_183 = C_184
      | ~ r2_relset_1(A_185,B_186,C_184,D_183)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_645,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_637])).

tff(c_660,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_645])).

tff(c_661,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_722,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_711,c_661])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_722])).

tff(c_747,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_1049,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k2_relset_1(A_279,B_280,C_281) = B_280
      | ~ r2_relset_1(B_280,B_280,k1_partfun1(B_280,A_279,A_279,B_280,D_282,C_281),k6_partfun1(B_280))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(B_280,A_279)))
      | ~ v1_funct_2(D_282,B_280,A_279)
      | ~ v1_funct_1(D_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_2(C_281,A_279,B_280)
      | ~ v1_funct_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1052,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_1049])).

tff(c_1054,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_582,c_616,c_1052])).

tff(c_28,plain,(
    ! [B_22] :
      ( v2_funct_2(B_22,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1059,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_28])).

tff(c_1063,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_555,c_1054,c_1059])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_1063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.65  
% 3.60/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.65  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.60/1.65  
% 3.60/1.65  %Foreground sorts:
% 3.60/1.65  
% 3.60/1.65  
% 3.60/1.65  %Background operators:
% 3.60/1.65  
% 3.60/1.65  
% 3.60/1.65  %Foreground operators:
% 3.60/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.60/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.60/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.60/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.65  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.60/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.65  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.60/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.60/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.60/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.60/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.60/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.65  
% 3.60/1.67  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 3.60/1.67  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.67  tff(f_38, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.60/1.67  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.60/1.67  tff(f_93, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.60/1.67  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.60/1.67  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.60/1.67  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.60/1.67  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.60/1.67  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.60/1.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.60/1.67  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.60/1.67  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.67  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.60/1.67  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.60/1.67  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_73, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.67  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_73])).
% 3.60/1.67  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_86, plain, (![A_48]: (v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.67  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_71, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.60/1.67  tff(c_89, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_86, c_71])).
% 3.60/1.67  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_89])).
% 3.60/1.67  tff(c_121, plain, (![C_57, A_58, B_59]: (v1_xboole_0(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.60/1.67  tff(c_130, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_121])).
% 3.60/1.67  tff(c_135, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_130])).
% 3.60/1.67  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_36, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.67  tff(c_10, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.60/1.67  tff(c_60, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 3.60/1.67  tff(c_260, plain, (![D_92, E_90, F_89, B_91, A_93, C_88]: (m1_subset_1(k1_partfun1(A_93, B_91, C_88, D_92, E_90, F_89), k1_zfmisc_1(k2_zfmisc_1(A_93, D_92))) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_88, D_92))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.60/1.67  tff(c_26, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.67  tff(c_59, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 3.60/1.67  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.60/1.67  tff(c_190, plain, (![D_73, C_74, A_75, B_76]: (D_73=C_74 | ~r2_relset_1(A_75, B_76, C_74, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.67  tff(c_198, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_190])).
% 3.60/1.67  tff(c_213, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_198])).
% 3.60/1.67  tff(c_227, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_213])).
% 3.60/1.67  tff(c_268, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_260, c_227])).
% 3.60/1.67  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_268])).
% 3.60/1.67  tff(c_292, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_213])).
% 3.60/1.67  tff(c_497, plain, (![E_151, D_150, B_152, A_148, C_149]: (k1_xboole_0=C_149 | v2_funct_1(D_150) | ~v2_funct_1(k1_partfun1(A_148, B_152, B_152, C_149, D_150, E_151)) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(B_152, C_149))) | ~v1_funct_2(E_151, B_152, C_149) | ~v1_funct_1(E_151) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_2(D_150, A_148, B_152) | ~v1_funct_1(D_150))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.60/1.67  tff(c_499, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_292, c_497])).
% 3.60/1.67  tff(c_504, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_60, c_499])).
% 3.60/1.67  tff(c_505, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_504])).
% 3.60/1.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.60/1.67  tff(c_509, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_2])).
% 3.60/1.67  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_509])).
% 3.60/1.67  tff(c_512, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.60/1.67  tff(c_515, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.67  tff(c_526, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_515])).
% 3.60/1.67  tff(c_544, plain, (![C_163, B_164, A_165]: (v5_relat_1(C_163, B_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.60/1.67  tff(c_555, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_544])).
% 3.60/1.67  tff(c_575, plain, (![A_172, B_173, D_174]: (r2_relset_1(A_172, B_173, D_174, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.67  tff(c_582, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_59, c_575])).
% 3.60/1.67  tff(c_605, plain, (![A_177, B_178, C_179]: (k2_relset_1(A_177, B_178, C_179)=k2_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.60/1.67  tff(c_616, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_605])).
% 3.60/1.67  tff(c_711, plain, (![C_200, D_204, B_203, A_205, F_201, E_202]: (m1_subset_1(k1_partfun1(A_205, B_203, C_200, D_204, E_202, F_201), k1_zfmisc_1(k2_zfmisc_1(A_205, D_204))) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_200, D_204))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_205, B_203))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.60/1.67  tff(c_637, plain, (![D_183, C_184, A_185, B_186]: (D_183=C_184 | ~r2_relset_1(A_185, B_186, C_184, D_183) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.67  tff(c_645, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_637])).
% 3.60/1.67  tff(c_660, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_645])).
% 3.60/1.67  tff(c_661, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_660])).
% 3.60/1.67  tff(c_722, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_711, c_661])).
% 3.60/1.67  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_722])).
% 3.60/1.67  tff(c_747, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_660])).
% 3.60/1.67  tff(c_1049, plain, (![A_279, B_280, C_281, D_282]: (k2_relset_1(A_279, B_280, C_281)=B_280 | ~r2_relset_1(B_280, B_280, k1_partfun1(B_280, A_279, A_279, B_280, D_282, C_281), k6_partfun1(B_280)) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(B_280, A_279))) | ~v1_funct_2(D_282, B_280, A_279) | ~v1_funct_1(D_282) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_2(C_281, A_279, B_280) | ~v1_funct_1(C_281))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.60/1.67  tff(c_1052, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_747, c_1049])).
% 3.60/1.67  tff(c_1054, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_582, c_616, c_1052])).
% 3.60/1.67  tff(c_28, plain, (![B_22]: (v2_funct_2(B_22, k2_relat_1(B_22)) | ~v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.60/1.67  tff(c_1059, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1054, c_28])).
% 3.60/1.67  tff(c_1063, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_555, c_1054, c_1059])).
% 3.60/1.67  tff(c_1065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_1063])).
% 3.60/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.67  
% 3.60/1.67  Inference rules
% 3.60/1.67  ----------------------
% 3.60/1.67  #Ref     : 0
% 3.60/1.67  #Sup     : 208
% 3.60/1.67  #Fact    : 0
% 3.60/1.67  #Define  : 0
% 3.60/1.67  #Split   : 10
% 3.60/1.67  #Chain   : 0
% 3.60/1.67  #Close   : 0
% 3.60/1.67  
% 3.60/1.67  Ordering : KBO
% 3.60/1.67  
% 3.60/1.67  Simplification rules
% 3.60/1.67  ----------------------
% 3.60/1.67  #Subsume      : 1
% 3.60/1.67  #Demod        : 138
% 3.60/1.67  #Tautology    : 37
% 3.60/1.67  #SimpNegUnit  : 4
% 3.60/1.67  #BackRed      : 6
% 3.60/1.67  
% 3.60/1.67  #Partial instantiations: 0
% 3.60/1.67  #Strategies tried      : 1
% 3.60/1.67  
% 3.60/1.67  Timing (in seconds)
% 3.60/1.67  ----------------------
% 3.60/1.67  Preprocessing        : 0.36
% 3.60/1.67  Parsing              : 0.20
% 3.60/1.67  CNF conversion       : 0.02
% 3.60/1.67  Main loop            : 0.48
% 3.60/1.67  Inferencing          : 0.19
% 3.60/1.67  Reduction            : 0.15
% 3.60/1.67  Demodulation         : 0.11
% 3.60/1.67  BG Simplification    : 0.02
% 3.60/1.67  Subsumption          : 0.08
% 3.60/1.68  Abstraction          : 0.02
% 3.60/1.68  MUC search           : 0.00
% 3.60/1.68  Cooper               : 0.00
% 3.60/1.68  Total                : 0.88
% 3.60/1.68  Index Insertion      : 0.00
% 3.60/1.68  Index Deletion       : 0.00
% 3.60/1.68  Index Matching       : 0.00
% 3.60/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
