%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 234 expanded)
%              Number of leaves         :   40 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  198 ( 719 expanded)
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

tff(f_154,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_77,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_91,plain,(
    ! [A_49] :
      ( v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_75,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_94,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_75])).

tff(c_97,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_60,c_94])).

tff(c_125,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_xboole_0(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_131])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_264,plain,(
    ! [D_92,E_90,F_89,B_91,A_93,C_88] :
      ( m1_subset_1(k1_partfun1(A_93,B_91,C_88,D_92,E_90,F_89),k1_zfmisc_1(k2_zfmisc_1(A_93,D_92)))
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_88,D_92)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_61,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_194,plain,(
    ! [D_73,C_74,A_75,B_76] :
      ( D_73 = C_74
      | ~ r2_relset_1(A_75,B_76,C_74,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_194])).

tff(c_217,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_202])).

tff(c_231,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_272,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_264,c_231])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_272])).

tff(c_296,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_501,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_501])).

tff(c_508,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_50,c_62,c_503])).

tff(c_509,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_508])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_513,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_2])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_513])).

tff(c_516,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_520,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_533,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_520])).

tff(c_534,plain,(
    ! [C_158,B_159,A_160] :
      ( v5_relat_1(C_158,B_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_546,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_534])).

tff(c_579,plain,(
    ! [A_171,B_172,D_173] :
      ( r2_relset_1(A_171,B_172,D_173,D_173)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_586,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_61,c_579])).

tff(c_610,plain,(
    ! [A_177,B_178,C_179] :
      ( k2_relset_1(A_177,B_178,C_179) = k2_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_622,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_610])).

tff(c_34,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] :
      ( m1_subset_1(k1_partfun1(A_23,B_24,C_25,D_26,E_27,F_28),k1_zfmisc_1(k2_zfmisc_1(A_23,D_26)))
      | ~ m1_subset_1(F_28,k1_zfmisc_1(k2_zfmisc_1(C_25,D_26)))
      | ~ v1_funct_1(F_28)
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(E_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_641,plain,(
    ! [D_182,C_183,A_184,B_185] :
      ( D_182 = C_183
      | ~ r2_relset_1(A_184,B_185,C_183,D_182)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_649,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_641])).

tff(c_664,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_649])).

tff(c_770,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_773,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_770])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_773])).

tff(c_778,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_940,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k2_relset_1(A_258,B_259,C_260) = B_259
      | ~ r2_relset_1(B_259,B_259,k1_partfun1(B_259,A_258,A_258,B_259,D_261,C_260),k6_partfun1(B_259))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(B_259,A_258)))
      | ~ v1_funct_2(D_261,B_259,A_258)
      | ~ v1_funct_1(D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_943,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_940])).

tff(c_945,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_56,c_586,c_622,c_943])).

tff(c_30,plain,(
    ! [B_22] :
      ( v2_funct_2(B_22,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_950,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_30])).

tff(c_954,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_546,c_945,c_950])).

tff(c_956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.60  
% 3.44/1.60  %Foreground sorts:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Background operators:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Foreground operators:
% 3.44/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.44/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.60  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.44/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.60  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.44/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.60  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.60  
% 3.44/1.62  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 3.44/1.62  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.44/1.62  tff(f_38, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.44/1.62  tff(f_59, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.44/1.62  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.44/1.62  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.44/1.62  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.44/1.62  tff(f_73, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.44/1.62  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.44/1.62  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.44/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.44/1.62  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.62  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.44/1.62  tff(f_112, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.44/1.62  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.44/1.62  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_77, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.44/1.62  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_77])).
% 3.44/1.62  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_91, plain, (![A_49]: (v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.62  tff(c_46, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_75, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.44/1.62  tff(c_94, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_91, c_75])).
% 3.44/1.62  tff(c_97, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_60, c_94])).
% 3.44/1.62  tff(c_125, plain, (![C_57, A_58, B_59]: (v1_xboole_0(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.62  tff(c_131, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_125])).
% 3.44/1.62  tff(c_138, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_97, c_131])).
% 3.44/1.62  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_38, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.44/1.62  tff(c_12, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.62  tff(c_62, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 3.44/1.62  tff(c_264, plain, (![D_92, E_90, F_89, B_91, A_93, C_88]: (m1_subset_1(k1_partfun1(A_93, B_91, C_88, D_92, E_90, F_89), k1_zfmisc_1(k2_zfmisc_1(A_93, D_92))) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_88, D_92))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.62  tff(c_28, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.62  tff(c_61, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 3.44/1.62  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.62  tff(c_194, plain, (![D_73, C_74, A_75, B_76]: (D_73=C_74 | ~r2_relset_1(A_75, B_76, C_74, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.62  tff(c_202, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_194])).
% 3.44/1.62  tff(c_217, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_202])).
% 3.44/1.62  tff(c_231, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_217])).
% 3.44/1.62  tff(c_272, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_264, c_231])).
% 3.44/1.62  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_272])).
% 3.44/1.62  tff(c_296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 3.44/1.62  tff(c_501, plain, (![E_151, D_150, B_152, A_148, C_149]: (k1_xboole_0=C_149 | v2_funct_1(D_150) | ~v2_funct_1(k1_partfun1(A_148, B_152, B_152, C_149, D_150, E_151)) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(B_152, C_149))) | ~v1_funct_2(E_151, B_152, C_149) | ~v1_funct_1(E_151) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_2(D_150, A_148, B_152) | ~v1_funct_1(D_150))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.44/1.62  tff(c_503, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_296, c_501])).
% 3.44/1.62  tff(c_508, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_50, c_62, c_503])).
% 3.44/1.62  tff(c_509, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_508])).
% 3.44/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.44/1.62  tff(c_513, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_2])).
% 3.44/1.62  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_513])).
% 3.44/1.62  tff(c_516, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.44/1.62  tff(c_520, plain, (![C_155, A_156, B_157]: (v1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.44/1.62  tff(c_533, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_520])).
% 3.44/1.62  tff(c_534, plain, (![C_158, B_159, A_160]: (v5_relat_1(C_158, B_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.44/1.62  tff(c_546, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_534])).
% 3.44/1.62  tff(c_579, plain, (![A_171, B_172, D_173]: (r2_relset_1(A_171, B_172, D_173, D_173) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.62  tff(c_586, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_61, c_579])).
% 3.44/1.62  tff(c_610, plain, (![A_177, B_178, C_179]: (k2_relset_1(A_177, B_178, C_179)=k2_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.62  tff(c_622, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_610])).
% 3.44/1.62  tff(c_34, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (m1_subset_1(k1_partfun1(A_23, B_24, C_25, D_26, E_27, F_28), k1_zfmisc_1(k2_zfmisc_1(A_23, D_26))) | ~m1_subset_1(F_28, k1_zfmisc_1(k2_zfmisc_1(C_25, D_26))) | ~v1_funct_1(F_28) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(E_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.62  tff(c_641, plain, (![D_182, C_183, A_184, B_185]: (D_182=C_183 | ~r2_relset_1(A_184, B_185, C_183, D_182) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.62  tff(c_649, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_641])).
% 3.44/1.62  tff(c_664, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_649])).
% 3.44/1.62  tff(c_770, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_664])).
% 3.44/1.62  tff(c_773, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_770])).
% 3.44/1.62  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_773])).
% 3.44/1.62  tff(c_778, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_664])).
% 3.44/1.62  tff(c_940, plain, (![A_258, B_259, C_260, D_261]: (k2_relset_1(A_258, B_259, C_260)=B_259 | ~r2_relset_1(B_259, B_259, k1_partfun1(B_259, A_258, A_258, B_259, D_261, C_260), k6_partfun1(B_259)) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(B_259, A_258))) | ~v1_funct_2(D_261, B_259, A_258) | ~v1_funct_1(D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.44/1.62  tff(c_943, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_778, c_940])).
% 3.44/1.62  tff(c_945, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_56, c_586, c_622, c_943])).
% 3.44/1.62  tff(c_30, plain, (![B_22]: (v2_funct_2(B_22, k2_relat_1(B_22)) | ~v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_950, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_945, c_30])).
% 3.44/1.62  tff(c_954, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_546, c_945, c_950])).
% 3.44/1.62  tff(c_956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_516, c_954])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 185
% 3.44/1.62  #Fact    : 0
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 9
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 1
% 3.44/1.62  #Demod        : 132
% 3.44/1.62  #Tautology    : 39
% 3.44/1.62  #SimpNegUnit  : 4
% 3.44/1.62  #BackRed      : 7
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 0
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.36
% 3.44/1.62  Parsing              : 0.20
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.45
% 3.44/1.62  Inferencing          : 0.17
% 3.44/1.62  Reduction            : 0.14
% 3.44/1.62  Demodulation         : 0.10
% 3.44/1.62  BG Simplification    : 0.02
% 3.44/1.62  Subsumption          : 0.07
% 3.44/1.62  Abstraction          : 0.02
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.85
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
