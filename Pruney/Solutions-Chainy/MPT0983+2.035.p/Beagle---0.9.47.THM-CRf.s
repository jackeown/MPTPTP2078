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
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 214 expanded)
%              Number of leaves         :   41 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 704 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_75,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_75])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_88,plain,(
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

tff(c_73,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_91,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_73])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60,c_91])).

tff(c_125,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_131])).

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

tff(c_10,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_261,plain,(
    ! [C_89,D_92,E_90,F_91,A_88,B_93] :
      ( m1_subset_1(k1_partfun1(A_88,B_93,C_89,D_92,E_90,F_91),k1_zfmisc_1(k2_zfmisc_1(A_88,D_92)))
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_89,D_92)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_93)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_188,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( D_74 = C_75
      | ~ r2_relset_1(A_76,B_77,C_75,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_196,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_211,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_196])).

tff(c_229,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_269,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_261,c_229])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_269])).

tff(c_293,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_498,plain,(
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

tff(c_500,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_498])).

tff(c_505,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_50,c_61,c_500])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_505])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_510,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_2])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_510])).

tff(c_513,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_517,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_529,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_517])).

tff(c_530,plain,(
    ! [C_158,B_159,A_160] :
      ( v5_relat_1(C_158,B_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_542,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_530])).

tff(c_576,plain,(
    ! [A_172,B_173,D_174] :
      ( r2_relset_1(A_172,B_173,D_174,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_583,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_36,c_576])).

tff(c_606,plain,(
    ! [A_177,B_178,C_179] :
      ( k2_relset_1(A_177,B_178,C_179) = k2_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_618,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_606])).

tff(c_712,plain,(
    ! [A_200,F_203,D_204,B_205,E_202,C_201] :
      ( m1_subset_1(k1_partfun1(A_200,B_205,C_201,D_204,E_202,F_203),k1_zfmisc_1(k2_zfmisc_1(A_200,D_204)))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_201,D_204)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_205)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_638,plain,(
    ! [D_183,C_184,A_185,B_186] :
      ( D_183 = C_184
      | ~ r2_relset_1(A_185,B_186,C_184,D_183)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_646,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_638])).

tff(c_661,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_646])).

tff(c_662,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_723,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_712,c_662])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_723])).

tff(c_748,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_1016,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_relset_1(A_283,B_284,C_285) = B_284
      | ~ r2_relset_1(B_284,B_284,k1_partfun1(B_284,A_283,A_283,B_284,D_286,C_285),k6_partfun1(B_284))
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(B_284,A_283)))
      | ~ v1_funct_2(D_286,B_284,A_283)
      | ~ v1_funct_1(D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_2(C_285,A_283,B_284)
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1019,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_1016])).

tff(c_1021,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_56,c_583,c_618,c_1019])).

tff(c_26,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1026,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_26])).

tff(c_1030,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_542,c_1021,c_1026])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_1030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:16:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.58  
% 3.61/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.58  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.58  
% 3.61/1.58  %Foreground sorts:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Background operators:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Foreground operators:
% 3.61/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.61/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.58  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.61/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.58  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.61/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.58  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.61/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.61/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.58  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.61/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.58  
% 3.68/1.60  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 3.68/1.60  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.68/1.60  tff(f_38, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.68/1.60  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.68/1.60  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.68/1.60  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.68/1.60  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.68/1.60  tff(f_93, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.68/1.60  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.68/1.60  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.68/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.68/1.60  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.68/1.60  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.68/1.60  tff(f_112, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.68/1.60  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.68/1.60  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_75, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.60  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_75])).
% 3.68/1.60  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_88, plain, (![A_49]: (v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.60  tff(c_46, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_73, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.68/1.60  tff(c_91, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_88, c_73])).
% 3.68/1.60  tff(c_94, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60, c_91])).
% 3.68/1.60  tff(c_125, plain, (![C_60, A_61, B_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.68/1.60  tff(c_131, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_125])).
% 3.68/1.60  tff(c_138, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_94, c_131])).
% 3.68/1.60  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_38, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.68/1.60  tff(c_10, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.68/1.60  tff(c_61, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 3.68/1.60  tff(c_261, plain, (![C_89, D_92, E_90, F_91, A_88, B_93]: (m1_subset_1(k1_partfun1(A_88, B_93, C_89, D_92, E_90, F_91), k1_zfmisc_1(k2_zfmisc_1(A_88, D_92))) | ~m1_subset_1(F_91, k1_zfmisc_1(k2_zfmisc_1(C_89, D_92))) | ~v1_funct_1(F_91) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_93))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.68/1.60  tff(c_36, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.68/1.60  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.68/1.60  tff(c_188, plain, (![D_74, C_75, A_76, B_77]: (D_74=C_75 | ~r2_relset_1(A_76, B_77, C_75, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.68/1.60  tff(c_196, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_188])).
% 3.68/1.60  tff(c_211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_196])).
% 3.68/1.60  tff(c_229, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_211])).
% 3.68/1.60  tff(c_269, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_261, c_229])).
% 3.68/1.60  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_269])).
% 3.68/1.60  tff(c_293, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_211])).
% 3.68/1.60  tff(c_498, plain, (![E_151, D_150, B_152, A_148, C_149]: (k1_xboole_0=C_149 | v2_funct_1(D_150) | ~v2_funct_1(k1_partfun1(A_148, B_152, B_152, C_149, D_150, E_151)) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(B_152, C_149))) | ~v1_funct_2(E_151, B_152, C_149) | ~v1_funct_1(E_151) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_2(D_150, A_148, B_152) | ~v1_funct_1(D_150))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.68/1.60  tff(c_500, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_293, c_498])).
% 3.68/1.60  tff(c_505, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_50, c_61, c_500])).
% 3.68/1.60  tff(c_506, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_505])).
% 3.68/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.68/1.60  tff(c_510, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_2])).
% 3.68/1.60  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_510])).
% 3.68/1.60  tff(c_513, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.68/1.60  tff(c_517, plain, (![C_155, A_156, B_157]: (v1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.60  tff(c_529, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_517])).
% 3.68/1.60  tff(c_530, plain, (![C_158, B_159, A_160]: (v5_relat_1(C_158, B_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.68/1.60  tff(c_542, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_530])).
% 3.68/1.60  tff(c_576, plain, (![A_172, B_173, D_174]: (r2_relset_1(A_172, B_173, D_174, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.68/1.60  tff(c_583, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_36, c_576])).
% 3.68/1.60  tff(c_606, plain, (![A_177, B_178, C_179]: (k2_relset_1(A_177, B_178, C_179)=k2_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.68/1.60  tff(c_618, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_606])).
% 3.68/1.60  tff(c_712, plain, (![A_200, F_203, D_204, B_205, E_202, C_201]: (m1_subset_1(k1_partfun1(A_200, B_205, C_201, D_204, E_202, F_203), k1_zfmisc_1(k2_zfmisc_1(A_200, D_204))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_201, D_204))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_205))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.68/1.60  tff(c_638, plain, (![D_183, C_184, A_185, B_186]: (D_183=C_184 | ~r2_relset_1(A_185, B_186, C_184, D_183) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.68/1.60  tff(c_646, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_638])).
% 3.68/1.60  tff(c_661, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_646])).
% 3.68/1.60  tff(c_662, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_661])).
% 3.68/1.60  tff(c_723, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_712, c_662])).
% 3.68/1.60  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_723])).
% 3.68/1.60  tff(c_748, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_661])).
% 3.68/1.60  tff(c_1016, plain, (![A_283, B_284, C_285, D_286]: (k2_relset_1(A_283, B_284, C_285)=B_284 | ~r2_relset_1(B_284, B_284, k1_partfun1(B_284, A_283, A_283, B_284, D_286, C_285), k6_partfun1(B_284)) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(B_284, A_283))) | ~v1_funct_2(D_286, B_284, A_283) | ~v1_funct_1(D_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_2(C_285, A_283, B_284) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.60  tff(c_1019, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_748, c_1016])).
% 3.68/1.60  tff(c_1021, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_56, c_583, c_618, c_1019])).
% 3.68/1.60  tff(c_26, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.68/1.60  tff(c_1026, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_26])).
% 3.68/1.60  tff(c_1030, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_529, c_542, c_1021, c_1026])).
% 3.68/1.60  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_513, c_1030])).
% 3.68/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.60  
% 3.68/1.60  Inference rules
% 3.68/1.60  ----------------------
% 3.68/1.60  #Ref     : 0
% 3.68/1.60  #Sup     : 203
% 3.68/1.60  #Fact    : 0
% 3.68/1.60  #Define  : 0
% 3.68/1.60  #Split   : 9
% 3.68/1.60  #Chain   : 0
% 3.68/1.60  #Close   : 0
% 3.68/1.60  
% 3.68/1.60  Ordering : KBO
% 3.68/1.60  
% 3.68/1.60  Simplification rules
% 3.68/1.60  ----------------------
% 3.68/1.60  #Subsume      : 1
% 3.68/1.60  #Demod        : 134
% 3.68/1.60  #Tautology    : 37
% 3.68/1.60  #SimpNegUnit  : 4
% 3.68/1.60  #BackRed      : 6
% 3.68/1.60  
% 3.68/1.60  #Partial instantiations: 0
% 3.68/1.60  #Strategies tried      : 1
% 3.68/1.60  
% 3.68/1.60  Timing (in seconds)
% 3.68/1.60  ----------------------
% 3.68/1.61  Preprocessing        : 0.35
% 3.68/1.61  Parsing              : 0.20
% 3.68/1.61  CNF conversion       : 0.02
% 3.68/1.61  Main loop            : 0.47
% 3.68/1.61  Inferencing          : 0.18
% 3.68/1.61  Reduction            : 0.15
% 3.68/1.61  Demodulation         : 0.11
% 3.68/1.61  BG Simplification    : 0.02
% 3.68/1.61  Subsumption          : 0.08
% 3.68/1.61  Abstraction          : 0.02
% 3.68/1.61  MUC search           : 0.00
% 3.68/1.61  Cooper               : 0.00
% 3.68/1.61  Total                : 0.86
% 3.68/1.61  Index Insertion      : 0.00
% 3.68/1.61  Index Deletion       : 0.00
% 3.68/1.61  Index Matching       : 0.00
% 3.68/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
