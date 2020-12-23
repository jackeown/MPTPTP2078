%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 738 expanded)
%              Number of leaves         :   44 ( 287 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (2874 expanded)
%              Number of equality atoms :   57 ( 770 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_174,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_181,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_174])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_192,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_58])).

tff(c_79,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_79])).

tff(c_118,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_125,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_87,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_79])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_62,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_148,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_156,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_148])).

tff(c_297,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_303,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_297])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_156,c_303])).

tff(c_310,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_309])).

tff(c_234,plain,(
    ! [A_83] :
      ( k2_relat_1(k5_relat_1(A_83,k2_funct_1(A_83))) = k1_relat_1(A_83)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_367,plain,(
    ! [A_114] :
      ( r1_tarski(k1_relat_1(A_114),k2_relat_1(k2_funct_1(A_114)))
      | ~ v1_relat_1(k2_funct_1(A_114))
      | ~ v1_relat_1(A_114)
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_378,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_367])).

tff(c_387,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_70,c_62,c_87,c_378])).

tff(c_388,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_391,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_388])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_70,c_62,c_391])).

tff(c_397,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_26,plain,(
    ! [A_16] :
      ( k2_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_126,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_398,plain,(
    ! [F_118,D_120,E_117,A_115,C_119,B_116] :
      ( k1_partfun1(A_115,B_116,C_119,D_120,E_117,F_118) = k5_relat_1(E_117,F_118)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_119,D_120)))
      | ~ v1_funct_1(F_118)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_402,plain,(
    ! [A_115,B_116,E_117] :
      ( k1_partfun1(A_115,B_116,'#skF_2','#skF_3',E_117,'#skF_5') = k5_relat_1(E_117,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(E_117) ) ),
    inference(resolution,[status(thm)],[c_66,c_398])).

tff(c_643,plain,(
    ! [A_132,B_133,E_134] :
      ( k1_partfun1(A_132,B_133,'#skF_2','#skF_3',E_134,'#skF_5') = k5_relat_1(E_134,'#skF_5')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_402])).

tff(c_655,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_643])).

tff(c_668,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_655])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_673,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_64])).

tff(c_52,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_677,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_52])).

tff(c_681,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_677])).

tff(c_38,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_711,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_681,c_38])).

tff(c_749,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_711])).

tff(c_127,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [B_81,A_82] :
      ( k2_relat_1(B_81) = A_82
      | ~ r1_tarski(A_82,k2_relat_1(B_81))
      | ~ v5_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_229,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_213])).

tff(c_777,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_229])).

tff(c_811,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87,c_126,c_749,c_777])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_844,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_12])).

tff(c_1001,plain,(
    ! [B_145] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_145)) = k9_relat_1(B_145,'#skF_3')
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_844])).

tff(c_1054,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1001])).

tff(c_1068,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_70,c_62,c_397,c_310,c_1054])).

tff(c_201,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k2_funct_1(B_79),A_80) = k9_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,k10_relat_1(B_13,A_12)),A_12)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_898,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_138),k9_relat_1(B_138,A_139)),A_139)
      | ~ v1_funct_1(k2_funct_1(B_138))
      | ~ v1_relat_1(k2_funct_1(B_138))
      | ~ v2_funct_1(B_138)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_22])).

tff(c_3956,plain,(
    ! [B_283,A_284] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_283),k2_relat_1(k5_relat_1(A_284,B_283))),k2_relat_1(A_284))
      | ~ v1_funct_1(k2_funct_1(B_283))
      | ~ v1_relat_1(k2_funct_1(B_283))
      | ~ v2_funct_1(B_283)
      | ~ v1_funct_1(B_283)
      | ~ v1_relat_1(B_283)
      | ~ v1_relat_1(B_283)
      | ~ v1_relat_1(A_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_898])).

tff(c_3985,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_5'),'#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_3956])).

tff(c_4007,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87,c_87,c_70,c_62,c_397,c_1068,c_3985])).

tff(c_4010,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4007])).

tff(c_4013,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_4010])).

tff(c_4017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_70,c_62,c_4013])).

tff(c_4018,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4007])).

tff(c_134,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(B_63) = A_64
      | ~ r1_tarski(A_64,k2_relat_1(B_63))
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_4023,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4018,c_134])).

tff(c_4028,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_125,c_4023])).

tff(c_4030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_4028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.26/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.67  
% 7.32/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.32/2.67  
% 7.32/2.67  %Foreground sorts:
% 7.32/2.67  
% 7.32/2.67  
% 7.32/2.67  %Background operators:
% 7.32/2.67  
% 7.32/2.67  
% 7.32/2.67  %Foreground operators:
% 7.32/2.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.32/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.32/2.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.32/2.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.32/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.32/2.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.32/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.32/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.32/2.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.32/2.67  tff('#skF_5', type, '#skF_5': $i).
% 7.32/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.32/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.32/2.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.32/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.32/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.32/2.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.32/2.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.32/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.32/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.32/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.32/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.32/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.32/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.32/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.32/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.32/2.67  
% 7.32/2.69  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 7.32/2.69  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.32/2.69  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.32/2.69  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.32/2.69  tff(f_63, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.32/2.69  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.32/2.69  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.32/2.69  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.32/2.69  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.32/2.69  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.32/2.69  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.32/2.69  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.32/2.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.32/2.69  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 7.32/2.69  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 7.32/2.69  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 7.32/2.69  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_174, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.32/2.69  tff(c_181, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_174])).
% 7.32/2.69  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_192, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_58])).
% 7.32/2.69  tff(c_79, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.32/2.69  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_79])).
% 7.32/2.69  tff(c_118, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.32/2.69  tff(c_125, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_118])).
% 7.32/2.69  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_87, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_79])).
% 7.32/2.69  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_62, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_18, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.32/2.69  tff(c_20, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.32/2.69  tff(c_60, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_148, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.32/2.69  tff(c_156, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_148])).
% 7.32/2.69  tff(c_297, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.32/2.69  tff(c_303, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_297])).
% 7.32/2.69  tff(c_309, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_156, c_303])).
% 7.32/2.69  tff(c_310, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_309])).
% 7.32/2.69  tff(c_234, plain, (![A_83]: (k2_relat_1(k5_relat_1(A_83, k2_funct_1(A_83)))=k1_relat_1(A_83) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.32/2.69  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.32/2.69  tff(c_367, plain, (![A_114]: (r1_tarski(k1_relat_1(A_114), k2_relat_1(k2_funct_1(A_114))) | ~v1_relat_1(k2_funct_1(A_114)) | ~v1_relat_1(A_114) | ~v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 7.32/2.69  tff(c_378, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_310, c_367])).
% 7.32/2.69  tff(c_387, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_70, c_62, c_87, c_378])).
% 7.32/2.69  tff(c_388, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_387])).
% 7.32/2.69  tff(c_391, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_388])).
% 7.32/2.69  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_70, c_62, c_391])).
% 7.32/2.69  tff(c_397, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_387])).
% 7.32/2.69  tff(c_26, plain, (![A_16]: (k2_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.32/2.69  tff(c_126, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_118])).
% 7.32/2.69  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_398, plain, (![F_118, D_120, E_117, A_115, C_119, B_116]: (k1_partfun1(A_115, B_116, C_119, D_120, E_117, F_118)=k5_relat_1(E_117, F_118) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_119, D_120))) | ~v1_funct_1(F_118) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.32/2.69  tff(c_402, plain, (![A_115, B_116, E_117]: (k1_partfun1(A_115, B_116, '#skF_2', '#skF_3', E_117, '#skF_5')=k5_relat_1(E_117, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(E_117))), inference(resolution, [status(thm)], [c_66, c_398])).
% 7.32/2.69  tff(c_643, plain, (![A_132, B_133, E_134]: (k1_partfun1(A_132, B_133, '#skF_2', '#skF_3', E_134, '#skF_5')=k5_relat_1(E_134, '#skF_5') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(E_134))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_402])).
% 7.32/2.69  tff(c_655, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_643])).
% 7.32/2.69  tff(c_668, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_655])).
% 7.32/2.69  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.32/2.69  tff(c_673, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_64])).
% 7.32/2.69  tff(c_52, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.32/2.69  tff(c_677, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_668, c_52])).
% 7.32/2.69  tff(c_681, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_677])).
% 7.32/2.69  tff(c_38, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.32/2.69  tff(c_711, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_681, c_38])).
% 7.32/2.69  tff(c_749, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_711])).
% 7.32/2.69  tff(c_127, plain, (![B_63, A_64]: (r1_tarski(k2_relat_1(B_63), A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.32/2.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.32/2.69  tff(c_213, plain, (![B_81, A_82]: (k2_relat_1(B_81)=A_82 | ~r1_tarski(A_82, k2_relat_1(B_81)) | ~v5_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_127, c_2])).
% 7.32/2.69  tff(c_229, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_213])).
% 7.32/2.69  tff(c_777, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_749, c_229])).
% 7.32/2.69  tff(c_811, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87, c_126, c_749, c_777])).
% 7.32/2.69  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.32/2.69  tff(c_844, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_811, c_12])).
% 7.32/2.69  tff(c_1001, plain, (![B_145]: (k2_relat_1(k5_relat_1('#skF_5', B_145))=k9_relat_1(B_145, '#skF_3') | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_844])).
% 7.32/2.69  tff(c_1054, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1001])).
% 7.32/2.69  tff(c_1068, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_70, c_62, c_397, c_310, c_1054])).
% 7.32/2.69  tff(c_201, plain, (![B_79, A_80]: (k10_relat_1(k2_funct_1(B_79), A_80)=k9_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.32/2.69  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, k10_relat_1(B_13, A_12)), A_12) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.32/2.69  tff(c_898, plain, (![B_138, A_139]: (r1_tarski(k9_relat_1(k2_funct_1(B_138), k9_relat_1(B_138, A_139)), A_139) | ~v1_funct_1(k2_funct_1(B_138)) | ~v1_relat_1(k2_funct_1(B_138)) | ~v2_funct_1(B_138) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(superposition, [status(thm), theory('equality')], [c_201, c_22])).
% 7.32/2.69  tff(c_3956, plain, (![B_283, A_284]: (r1_tarski(k9_relat_1(k2_funct_1(B_283), k2_relat_1(k5_relat_1(A_284, B_283))), k2_relat_1(A_284)) | ~v1_funct_1(k2_funct_1(B_283)) | ~v1_relat_1(k2_funct_1(B_283)) | ~v2_funct_1(B_283) | ~v1_funct_1(B_283) | ~v1_relat_1(B_283) | ~v1_relat_1(B_283) | ~v1_relat_1(A_284))), inference(superposition, [status(thm), theory('equality')], [c_12, c_898])).
% 7.32/2.69  tff(c_3985, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_5'), '#skF_3'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_749, c_3956])).
% 7.32/2.69  tff(c_4007, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87, c_87, c_70, c_62, c_397, c_1068, c_3985])).
% 7.32/2.69  tff(c_4010, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4007])).
% 7.32/2.69  tff(c_4013, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_4010])).
% 7.32/2.69  tff(c_4017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_70, c_62, c_4013])).
% 7.32/2.69  tff(c_4018, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4007])).
% 7.32/2.69  tff(c_134, plain, (![B_63, A_64]: (k2_relat_1(B_63)=A_64 | ~r1_tarski(A_64, k2_relat_1(B_63)) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_127, c_2])).
% 7.32/2.69  tff(c_4023, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4018, c_134])).
% 7.32/2.69  tff(c_4028, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_125, c_4023])).
% 7.32/2.69  tff(c_4030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_4028])).
% 7.32/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.69  
% 7.32/2.69  Inference rules
% 7.32/2.69  ----------------------
% 7.32/2.69  #Ref     : 0
% 7.32/2.69  #Sup     : 823
% 7.32/2.69  #Fact    : 0
% 7.32/2.69  #Define  : 0
% 7.32/2.69  #Split   : 17
% 7.32/2.69  #Chain   : 0
% 7.32/2.69  #Close   : 0
% 7.32/2.69  
% 7.32/2.69  Ordering : KBO
% 7.32/2.69  
% 7.32/2.69  Simplification rules
% 7.32/2.69  ----------------------
% 7.32/2.69  #Subsume      : 54
% 7.32/2.69  #Demod        : 978
% 7.32/2.69  #Tautology    : 166
% 7.32/2.69  #SimpNegUnit  : 41
% 7.32/2.69  #BackRed      : 42
% 7.32/2.69  
% 7.32/2.69  #Partial instantiations: 0
% 7.32/2.69  #Strategies tried      : 1
% 7.32/2.69  
% 7.32/2.69  Timing (in seconds)
% 7.32/2.69  ----------------------
% 7.32/2.70  Preprocessing        : 0.37
% 7.32/2.70  Parsing              : 0.20
% 7.32/2.70  CNF conversion       : 0.02
% 7.32/2.70  Main loop            : 1.55
% 7.32/2.70  Inferencing          : 0.48
% 7.32/2.70  Reduction            : 0.64
% 7.32/2.70  Demodulation         : 0.48
% 7.32/2.70  BG Simplification    : 0.05
% 7.32/2.70  Subsumption          : 0.28
% 7.32/2.70  Abstraction          : 0.05
% 7.32/2.70  MUC search           : 0.00
% 7.32/2.70  Cooper               : 0.00
% 7.32/2.70  Total                : 1.97
% 7.32/2.70  Index Insertion      : 0.00
% 7.32/2.70  Index Deletion       : 0.00
% 7.32/2.70  Index Matching       : 0.00
% 7.32/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
