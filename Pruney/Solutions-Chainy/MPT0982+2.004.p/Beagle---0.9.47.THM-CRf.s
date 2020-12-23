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
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 18.05s
% Output     : CNFRefutation 18.10s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 802 expanded)
%              Number of leaves         :   45 ( 305 expanded)
%              Depth                    :   22
%              Number of atoms          :  290 (3012 expanded)
%              Number of equality atoms :   72 ( 854 expanded)
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

tff(f_175,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_153,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_90,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_90])).

tff(c_127,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_134,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_127])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_198,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_191])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_200,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_60])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_98,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_174,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_182,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_174])).

tff(c_369,plain,(
    ! [B_103,A_104,C_105] :
      ( k1_xboole_0 = B_103
      | k1_relset_1(A_104,B_103,C_105) = A_104
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_375,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_369])).

tff(c_381,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_182,c_375])).

tff(c_382,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_381])).

tff(c_145,plain,(
    ! [A_66] :
      ( k2_relat_1(k2_funct_1(A_66)) = k1_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_54,A_55] :
      ( v5_relat_1(B_54,A_55)
      | ~ r1_tarski(k2_relat_1(B_54),A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [B_54] :
      ( v5_relat_1(B_54,k2_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_154,plain,(
    ! [A_66] :
      ( v5_relat_1(k2_funct_1(A_66),k1_relat_1(A_66))
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_104])).

tff(c_387,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_154])).

tff(c_391,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_72,c_64,c_387])).

tff(c_436,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_439,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_436])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_72,c_439])).

tff(c_445,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_135,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_127])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_446,plain,(
    ! [A_115,D_118,B_116,C_117,F_119,E_120] :
      ( k1_partfun1(A_115,B_116,C_117,D_118,E_120,F_119) = k5_relat_1(E_120,F_119)
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_117,D_118)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_450,plain,(
    ! [A_115,B_116,E_120] :
      ( k1_partfun1(A_115,B_116,'#skF_2','#skF_3',E_120,'#skF_5') = k5_relat_1(E_120,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_68,c_446])).

tff(c_932,plain,(
    ! [A_142,B_143,E_144] :
      ( k1_partfun1(A_142,B_143,'#skF_2','#skF_3',E_144,'#skF_5') = k5_relat_1(E_144,'#skF_5')
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_1(E_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_450])).

tff(c_944,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_932])).

tff(c_957,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_944])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_962,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_66])).

tff(c_54,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_966,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_54])).

tff(c_970,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_966])).

tff(c_40,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1000,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_970,c_40])).

tff(c_1038,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_1000])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(B_78) = A_79
      | ~ r1_tarski(A_79,k2_relat_1(B_78))
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_237,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_1072,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_237])).

tff(c_1111,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_98,c_135,c_1038,c_1072])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1155,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_12])).

tff(c_1381,plain,(
    ! [B_157] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_157)) = k9_relat_1(B_157,'#skF_3')
      | ~ v1_relat_1(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1155])).

tff(c_28,plain,(
    ! [A_17] :
      ( k2_relat_1(k5_relat_1(A_17,k2_funct_1(A_17))) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1421,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_28])).

tff(c_1462,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_98,c_72,c_64,c_382,c_1421])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(k2_funct_1(B_15),A_14) = k9_relat_1(B_15,A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_471,plain,(
    ! [A_124,A_125] :
      ( r1_tarski(k1_relat_1(A_124),A_125)
      | ~ v5_relat_1(k2_funct_1(A_124),A_125)
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_10])).

tff(c_488,plain,(
    ! [A_126] :
      ( r1_tarski(k1_relat_1(A_126),k2_relat_1(k2_funct_1(A_126)))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(k2_funct_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_104,c_471])).

tff(c_501,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_488])).

tff(c_517,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_98,c_72,c_64,c_501])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,k10_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_520,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_517,c_20])).

tff(c_531,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_520])).

tff(c_2149,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_2152,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_2149])).

tff(c_2156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_72,c_2152])).

tff(c_2158,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_444,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_126,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(B_60) = A_61
      | ~ r1_tarski(A_61,k2_relat_1(B_60))
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_523,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_517,c_126])).

tff(c_534,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_444,c_523])).

tff(c_611,plain,(
    ! [A_12] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_20])).

tff(c_647,plain,(
    ! [A_12] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_611])).

tff(c_5784,plain,(
    ! [A_335] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_335)) = A_335
      | ~ r1_tarski(A_335,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_647])).

tff(c_5839,plain,(
    ! [A_14] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_2')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5784])).

tff(c_5898,plain,(
    ! [A_338] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_338)) = A_338
      | ~ r1_tarski(A_338,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_72,c_64,c_5839])).

tff(c_5940,plain,(
    ! [A_5] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_5,'#skF_5'))) = k2_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5898])).

tff(c_25013,plain,(
    ! [A_866] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_866,'#skF_5'))) = k2_relat_1(A_866)
      | ~ r1_tarski(k2_relat_1(A_866),'#skF_2')
      | ~ v1_relat_1(A_866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5940])).

tff(c_25048,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_25013])).

tff(c_25069,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1462,c_25048])).

tff(c_25070,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_25069])).

tff(c_25075,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_25070])).

tff(c_25079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_134,c_25075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.05/8.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.05/8.67  
% 18.05/8.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.10/8.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 18.10/8.67  
% 18.10/8.67  %Foreground sorts:
% 18.10/8.67  
% 18.10/8.67  
% 18.10/8.67  %Background operators:
% 18.10/8.67  
% 18.10/8.67  
% 18.10/8.67  %Foreground operators:
% 18.10/8.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.10/8.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.10/8.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.10/8.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.10/8.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.10/8.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.10/8.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.10/8.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.10/8.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.10/8.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.10/8.67  tff('#skF_5', type, '#skF_5': $i).
% 18.10/8.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.10/8.67  tff('#skF_2', type, '#skF_2': $i).
% 18.10/8.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.10/8.67  tff('#skF_3', type, '#skF_3': $i).
% 18.10/8.67  tff('#skF_1', type, '#skF_1': $i).
% 18.10/8.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 18.10/8.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.10/8.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.10/8.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.10/8.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.10/8.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.10/8.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.10/8.67  tff('#skF_4', type, '#skF_4': $i).
% 18.10/8.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.10/8.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.10/8.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.10/8.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.10/8.67  
% 18.10/8.69  tff(f_175, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 18.10/8.69  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.10/8.69  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.10/8.69  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 18.10/8.69  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.10/8.69  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.10/8.69  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 18.10/8.69  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 18.10/8.69  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 18.10/8.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.10/8.69  tff(f_153, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 18.10/8.69  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 18.10/8.69  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 18.10/8.69  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 18.10/8.69  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 18.10/8.69  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 18.10/8.69  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 18.10/8.69  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_90, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.10/8.69  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_90])).
% 18.10/8.69  tff(c_127, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.10/8.69  tff(c_134, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_127])).
% 18.10/8.69  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.10/8.69  tff(c_191, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 18.10/8.69  tff(c_198, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_191])).
% 18.10/8.69  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_200, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_60])).
% 18.10/8.69  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_98, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_90])).
% 18.10/8.69  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_18, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.10/8.69  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_174, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.10/8.69  tff(c_182, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_174])).
% 18.10/8.69  tff(c_369, plain, (![B_103, A_104, C_105]: (k1_xboole_0=B_103 | k1_relset_1(A_104, B_103, C_105)=A_104 | ~v1_funct_2(C_105, A_104, B_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.10/8.69  tff(c_375, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_369])).
% 18.10/8.69  tff(c_381, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_182, c_375])).
% 18.10/8.69  tff(c_382, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_381])).
% 18.10/8.69  tff(c_145, plain, (![A_66]: (k2_relat_1(k2_funct_1(A_66))=k1_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.10/8.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.10/8.69  tff(c_99, plain, (![B_54, A_55]: (v5_relat_1(B_54, A_55) | ~r1_tarski(k2_relat_1(B_54), A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.10/8.69  tff(c_104, plain, (![B_54]: (v5_relat_1(B_54, k2_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_6, c_99])).
% 18.10/8.69  tff(c_154, plain, (![A_66]: (v5_relat_1(k2_funct_1(A_66), k1_relat_1(A_66)) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_145, c_104])).
% 18.10/8.69  tff(c_387, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_382, c_154])).
% 18.10/8.69  tff(c_391, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_72, c_64, c_387])).
% 18.10/8.69  tff(c_436, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_391])).
% 18.10/8.69  tff(c_439, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_436])).
% 18.10/8.69  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_72, c_439])).
% 18.10/8.69  tff(c_445, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_391])).
% 18.10/8.69  tff(c_135, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_127])).
% 18.10/8.69  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_446, plain, (![A_115, D_118, B_116, C_117, F_119, E_120]: (k1_partfun1(A_115, B_116, C_117, D_118, E_120, F_119)=k5_relat_1(E_120, F_119) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_117, D_118))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_153])).
% 18.10/8.69  tff(c_450, plain, (![A_115, B_116, E_120]: (k1_partfun1(A_115, B_116, '#skF_2', '#skF_3', E_120, '#skF_5')=k5_relat_1(E_120, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_68, c_446])).
% 18.10/8.69  tff(c_932, plain, (![A_142, B_143, E_144]: (k1_partfun1(A_142, B_143, '#skF_2', '#skF_3', E_144, '#skF_5')=k5_relat_1(E_144, '#skF_5') | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_1(E_144))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_450])).
% 18.10/8.69  tff(c_944, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_932])).
% 18.10/8.69  tff(c_957, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_944])).
% 18.10/8.69  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_175])).
% 18.10/8.69  tff(c_962, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_957, c_66])).
% 18.10/8.69  tff(c_54, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.10/8.69  tff(c_966, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_957, c_54])).
% 18.10/8.69  tff(c_970, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_966])).
% 18.10/8.69  tff(c_40, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 18.10/8.69  tff(c_1000, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_970, c_40])).
% 18.10/8.69  tff(c_1038, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_962, c_1000])).
% 18.10/8.69  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.10/8.69  tff(c_119, plain, (![B_60, A_61]: (r1_tarski(k2_relat_1(B_60), A_61) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.10/8.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.10/8.69  tff(c_222, plain, (![B_78, A_79]: (k2_relat_1(B_78)=A_79 | ~r1_tarski(A_79, k2_relat_1(B_78)) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_119, c_2])).
% 18.10/8.69  tff(c_237, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_222])).
% 18.10/8.69  tff(c_1072, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1038, c_237])).
% 18.10/8.69  tff(c_1111, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_98, c_135, c_1038, c_1072])).
% 18.10/8.69  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.10/8.69  tff(c_1155, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_12])).
% 18.10/8.69  tff(c_1381, plain, (![B_157]: (k2_relat_1(k5_relat_1('#skF_5', B_157))=k9_relat_1(B_157, '#skF_3') | ~v1_relat_1(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1155])).
% 18.10/8.69  tff(c_28, plain, (![A_17]: (k2_relat_1(k5_relat_1(A_17, k2_funct_1(A_17)))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.10/8.69  tff(c_1421, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_28])).
% 18.10/8.69  tff(c_1462, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_98, c_72, c_64, c_382, c_1421])).
% 18.10/8.69  tff(c_22, plain, (![B_15, A_14]: (k10_relat_1(k2_funct_1(B_15), A_14)=k9_relat_1(B_15, A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.10/8.69  tff(c_16, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.10/8.69  tff(c_471, plain, (![A_124, A_125]: (r1_tarski(k1_relat_1(A_124), A_125) | ~v5_relat_1(k2_funct_1(A_124), A_125) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_145, c_10])).
% 18.10/8.69  tff(c_488, plain, (![A_126]: (r1_tarski(k1_relat_1(A_126), k2_relat_1(k2_funct_1(A_126))) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126) | ~v1_relat_1(k2_funct_1(A_126)))), inference(resolution, [status(thm)], [c_104, c_471])).
% 18.10/8.69  tff(c_501, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_488])).
% 18.10/8.69  tff(c_517, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_98, c_72, c_64, c_501])).
% 18.10/8.69  tff(c_20, plain, (![B_13, A_12]: (k9_relat_1(B_13, k10_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k2_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.10/8.69  tff(c_520, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_517, c_20])).
% 18.10/8.69  tff(c_531, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_520])).
% 18.10/8.69  tff(c_2149, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_531])).
% 18.10/8.69  tff(c_2152, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_2149])).
% 18.10/8.69  tff(c_2156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_72, c_2152])).
% 18.10/8.69  tff(c_2158, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_531])).
% 18.10/8.69  tff(c_444, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_391])).
% 18.10/8.69  tff(c_126, plain, (![B_60, A_61]: (k2_relat_1(B_60)=A_61 | ~r1_tarski(A_61, k2_relat_1(B_60)) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_119, c_2])).
% 18.10/8.69  tff(c_523, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_517, c_126])).
% 18.10/8.69  tff(c_534, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_444, c_523])).
% 18.10/8.69  tff(c_611, plain, (![A_12]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_534, c_20])).
% 18.10/8.69  tff(c_647, plain, (![A_12]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_611])).
% 18.10/8.69  tff(c_5784, plain, (![A_335]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_335))=A_335 | ~r1_tarski(A_335, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_647])).
% 18.10/8.69  tff(c_5839, plain, (![A_14]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_14))=A_14 | ~r1_tarski(A_14, '#skF_2') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5784])).
% 18.10/8.69  tff(c_5898, plain, (![A_338]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_338))=A_338 | ~r1_tarski(A_338, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_72, c_64, c_5839])).
% 18.10/8.69  tff(c_5940, plain, (![A_5]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_5, '#skF_5')))=k2_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5898])).
% 18.10/8.69  tff(c_25013, plain, (![A_866]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_866, '#skF_5')))=k2_relat_1(A_866) | ~r1_tarski(k2_relat_1(A_866), '#skF_2') | ~v1_relat_1(A_866))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5940])).
% 18.10/8.69  tff(c_25048, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1038, c_25013])).
% 18.10/8.69  tff(c_25069, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1462, c_25048])).
% 18.10/8.69  tff(c_25070, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_200, c_25069])).
% 18.10/8.69  tff(c_25075, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_25070])).
% 18.10/8.69  tff(c_25079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_134, c_25075])).
% 18.10/8.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.10/8.69  
% 18.10/8.69  Inference rules
% 18.10/8.69  ----------------------
% 18.10/8.69  #Ref     : 0
% 18.10/8.69  #Sup     : 5291
% 18.10/8.69  #Fact    : 0
% 18.10/8.69  #Define  : 0
% 18.10/8.69  #Split   : 48
% 18.10/8.69  #Chain   : 0
% 18.10/8.69  #Close   : 0
% 18.10/8.69  
% 18.10/8.69  Ordering : KBO
% 18.10/8.69  
% 18.10/8.69  Simplification rules
% 18.10/8.69  ----------------------
% 18.10/8.69  #Subsume      : 782
% 18.10/8.69  #Demod        : 8326
% 18.10/8.69  #Tautology    : 1584
% 18.10/8.69  #SimpNegUnit  : 214
% 18.10/8.69  #BackRed      : 518
% 18.10/8.69  
% 18.10/8.69  #Partial instantiations: 0
% 18.10/8.69  #Strategies tried      : 1
% 18.10/8.69  
% 18.10/8.69  Timing (in seconds)
% 18.10/8.69  ----------------------
% 18.10/8.69  Preprocessing        : 0.38
% 18.10/8.69  Parsing              : 0.20
% 18.10/8.69  CNF conversion       : 0.03
% 18.10/8.70  Main loop            : 7.54
% 18.10/8.70  Inferencing          : 1.72
% 18.10/8.70  Reduction            : 3.64
% 18.10/8.70  Demodulation         : 2.98
% 18.10/8.70  BG Simplification    : 0.14
% 18.10/8.70  Subsumption          : 1.55
% 18.10/8.70  Abstraction          : 0.19
% 18.10/8.70  MUC search           : 0.00
% 18.10/8.70  Cooper               : 0.00
% 18.10/8.70  Total                : 7.96
% 18.10/8.70  Index Insertion      : 0.00
% 18.10/8.70  Index Deletion       : 0.00
% 18.10/8.70  Index Matching       : 0.00
% 18.10/8.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
