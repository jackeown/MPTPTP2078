%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 270 expanded)
%              Number of leaves         :   39 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 979 expanded)
%              Number of equality atoms :   61 ( 273 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_151,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_779,plain,(
    ! [B_129,A_127,C_130,E_131,F_126,D_128] :
      ( k1_partfun1(A_127,B_129,C_130,D_128,E_131,F_126) = k5_relat_1(E_131,F_126)
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_130,D_128)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_129)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_781,plain,(
    ! [A_127,B_129,E_131] :
      ( k1_partfun1(A_127,B_129,'#skF_2','#skF_3',E_131,'#skF_5') = k5_relat_1(E_131,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_129)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_56,c_779])).

tff(c_859,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_2','#skF_3',E_136,'#skF_5') = k5_relat_1(E_136,'#skF_5')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_781])).

tff(c_865,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_859])).

tff(c_871,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_865])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_878,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_54])).

tff(c_887,plain,(
    ! [C_137,D_142,F_139,B_138,E_141,A_140] :
      ( m1_subset_1(k1_partfun1(A_140,B_138,C_137,D_142,E_141,F_139),k1_zfmisc_1(k2_zfmisc_1(A_140,D_142)))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_137,D_142)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_936,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_887])).

tff(c_956,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_936])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_relset_1(A_24,B_25,C_26) = k2_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_983,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_956,c_28])).

tff(c_1016,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_983])).

tff(c_233,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_241,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_233])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_246,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_48])).

tff(c_76,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_91,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_99,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_60,B_61] :
      ( k8_relat_1(A_60,B_61) = B_61
      | ~ r1_tarski(k2_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_153,plain,(
    ! [A_65,B_66] :
      ( k8_relat_1(A_65,B_66) = B_66
      | ~ v5_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_159,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_153])).

tff(c_166,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_159])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_52,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_251,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_258,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_251])).

tff(c_467,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_470,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_467])).

tff(c_476,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_258,c_470])).

tff(c_477,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_476])).

tff(c_492,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_relat_1(A_102),k2_relat_1(B_103))
      | ~ v2_funct_1(A_102)
      | k2_relat_1(k5_relat_1(B_103,A_102)) != k2_relat_1(A_102)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_506,plain,(
    ! [B_103] :
      ( r1_tarski('#skF_2',k2_relat_1(B_103))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_103,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_492])).

tff(c_531,plain,(
    ! [B_104] :
      ( r1_tarski('#skF_2',k2_relat_1(B_104))
      | k2_relat_1(k5_relat_1(B_104,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_60,c_52,c_506])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k2_relat_1(k8_relat_1(A_5,B_6)) = A_5
      | ~ r1_tarski(A_5,k2_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_552,plain,(
    ! [B_105] :
      ( k2_relat_1(k8_relat_1('#skF_2',B_105)) = '#skF_2'
      | k2_relat_1(k5_relat_1(B_105,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_531,c_12])).

tff(c_608,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_552])).

tff(c_613,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_608])).

tff(c_614,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_613])).

tff(c_1020,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_614])).

tff(c_98,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_162,plain,
    ( k8_relat_1('#skF_3','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_153])).

tff(c_169,plain,(
    k8_relat_1('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_162])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_9,B_11)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_178,plain,(
    ! [A_67,B_68] :
      ( k2_relat_1(k8_relat_1(A_67,B_68)) = A_67
      | ~ r1_tarski(A_67,k2_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_190,plain,(
    ! [A_9,B_11] :
      ( k2_relat_1(k8_relat_1(k2_relat_1(k5_relat_1(A_9,B_11)),B_11)) = k2_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_178])).

tff(c_1062,plain,
    ( k2_relat_1(k8_relat_1('#skF_3','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_190])).

tff(c_1135,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_1016,c_169,c_1062])).

tff(c_1166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_1135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.68  
% 3.77/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.77/1.68  
% 3.77/1.68  %Foreground sorts:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Background operators:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Foreground operators:
% 3.77/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.68  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.77/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.77/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.77/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.68  
% 3.77/1.70  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 3.77/1.70  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.77/1.70  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.77/1.70  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.77/1.70  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.77/1.70  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.77/1.70  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.77/1.70  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.77/1.70  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.77/1.70  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.77/1.70  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 3.77/1.70  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 3.77/1.70  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.77/1.70  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_779, plain, (![B_129, A_127, C_130, E_131, F_126, D_128]: (k1_partfun1(A_127, B_129, C_130, D_128, E_131, F_126)=k5_relat_1(E_131, F_126) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_130, D_128))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_129))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.77/1.70  tff(c_781, plain, (![A_127, B_129, E_131]: (k1_partfun1(A_127, B_129, '#skF_2', '#skF_3', E_131, '#skF_5')=k5_relat_1(E_131, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_129))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_56, c_779])).
% 3.77/1.70  tff(c_859, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_2', '#skF_3', E_136, '#skF_5')=k5_relat_1(E_136, '#skF_5') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_781])).
% 3.77/1.70  tff(c_865, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_859])).
% 3.77/1.70  tff(c_871, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_865])).
% 3.77/1.70  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_878, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_871, c_54])).
% 3.77/1.70  tff(c_887, plain, (![C_137, D_142, F_139, B_138, E_141, A_140]: (m1_subset_1(k1_partfun1(A_140, B_138, C_137, D_142, E_141, F_139), k1_zfmisc_1(k2_zfmisc_1(A_140, D_142))) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_137, D_142))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.77/1.70  tff(c_936, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_871, c_887])).
% 3.77/1.70  tff(c_956, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_936])).
% 3.77/1.70  tff(c_28, plain, (![A_24, B_25, C_26]: (k2_relset_1(A_24, B_25, C_26)=k2_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.77/1.70  tff(c_983, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_956, c_28])).
% 3.77/1.70  tff(c_1016, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_878, c_983])).
% 3.77/1.70  tff(c_233, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.77/1.70  tff(c_241, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_233])).
% 3.77/1.70  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_246, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_48])).
% 3.77/1.70  tff(c_76, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.77/1.70  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_76])).
% 3.77/1.70  tff(c_91, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.77/1.70  tff(c_99, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_91])).
% 3.77/1.70  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.70  tff(c_122, plain, (![A_60, B_61]: (k8_relat_1(A_60, B_61)=B_61 | ~r1_tarski(k2_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.77/1.70  tff(c_153, plain, (![A_65, B_66]: (k8_relat_1(A_65, B_66)=B_66 | ~v5_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_10, c_122])).
% 3.77/1.70  tff(c_159, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_153])).
% 3.77/1.70  tff(c_166, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_159])).
% 3.77/1.70  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.77/1.70  tff(c_52, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.77/1.70  tff(c_251, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.77/1.70  tff(c_258, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_251])).
% 3.77/1.70  tff(c_467, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.77/1.70  tff(c_470, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_467])).
% 3.77/1.70  tff(c_476, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_258, c_470])).
% 3.77/1.70  tff(c_477, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_476])).
% 3.77/1.70  tff(c_492, plain, (![A_102, B_103]: (r1_tarski(k1_relat_1(A_102), k2_relat_1(B_103)) | ~v2_funct_1(A_102) | k2_relat_1(k5_relat_1(B_103, A_102))!=k2_relat_1(A_102) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.77/1.70  tff(c_506, plain, (![B_103]: (r1_tarski('#skF_2', k2_relat_1(B_103)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_103, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_103) | ~v1_relat_1(B_103) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_492])).
% 3.77/1.70  tff(c_531, plain, (![B_104]: (r1_tarski('#skF_2', k2_relat_1(B_104)) | k2_relat_1(k5_relat_1(B_104, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_60, c_52, c_506])).
% 3.77/1.70  tff(c_12, plain, (![A_5, B_6]: (k2_relat_1(k8_relat_1(A_5, B_6))=A_5 | ~r1_tarski(A_5, k2_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.70  tff(c_552, plain, (![B_105]: (k2_relat_1(k8_relat_1('#skF_2', B_105))='#skF_2' | k2_relat_1(k5_relat_1(B_105, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_531, c_12])).
% 3.77/1.70  tff(c_608, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_166, c_552])).
% 3.77/1.70  tff(c_613, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_608])).
% 3.77/1.70  tff(c_614, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_246, c_613])).
% 3.77/1.70  tff(c_1020, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_614])).
% 3.77/1.70  tff(c_98, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_91])).
% 3.77/1.70  tff(c_162, plain, (k8_relat_1('#skF_3', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_153])).
% 3.77/1.70  tff(c_169, plain, (k8_relat_1('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_162])).
% 3.77/1.70  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.77/1.70  tff(c_178, plain, (![A_67, B_68]: (k2_relat_1(k8_relat_1(A_67, B_68))=A_67 | ~r1_tarski(A_67, k2_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.70  tff(c_190, plain, (![A_9, B_11]: (k2_relat_1(k8_relat_1(k2_relat_1(k5_relat_1(A_9, B_11)), B_11))=k2_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_178])).
% 3.77/1.70  tff(c_1062, plain, (k2_relat_1(k8_relat_1('#skF_3', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1016, c_190])).
% 3.77/1.70  tff(c_1135, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_1016, c_169, c_1062])).
% 3.77/1.70  tff(c_1166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1020, c_1135])).
% 3.77/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.70  
% 3.77/1.70  Inference rules
% 3.77/1.70  ----------------------
% 3.77/1.70  #Ref     : 0
% 3.77/1.70  #Sup     : 281
% 3.77/1.70  #Fact    : 0
% 3.77/1.70  #Define  : 0
% 3.77/1.70  #Split   : 3
% 3.77/1.70  #Chain   : 0
% 3.77/1.70  #Close   : 0
% 3.77/1.70  
% 3.77/1.70  Ordering : KBO
% 3.77/1.70  
% 3.77/1.70  Simplification rules
% 3.77/1.70  ----------------------
% 3.77/1.70  #Subsume      : 18
% 3.77/1.70  #Demod        : 113
% 3.77/1.70  #Tautology    : 62
% 3.77/1.70  #SimpNegUnit  : 7
% 3.77/1.70  #BackRed      : 7
% 3.77/1.70  
% 3.77/1.70  #Partial instantiations: 0
% 3.77/1.70  #Strategies tried      : 1
% 3.77/1.70  
% 3.77/1.70  Timing (in seconds)
% 3.77/1.70  ----------------------
% 3.77/1.70  Preprocessing        : 0.38
% 3.77/1.70  Parsing              : 0.17
% 3.77/1.70  CNF conversion       : 0.03
% 3.77/1.70  Main loop            : 0.47
% 3.77/1.70  Inferencing          : 0.16
% 3.77/1.70  Reduction            : 0.15
% 3.77/1.70  Demodulation         : 0.11
% 3.77/1.70  BG Simplification    : 0.04
% 3.77/1.70  Subsumption          : 0.09
% 3.77/1.70  Abstraction          : 0.03
% 3.77/1.70  MUC search           : 0.00
% 3.77/1.70  Cooper               : 0.00
% 3.77/1.70  Total                : 0.90
% 3.77/1.70  Index Insertion      : 0.00
% 3.77/1.70  Index Deletion       : 0.00
% 3.77/1.70  Index Matching       : 0.00
% 3.77/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
