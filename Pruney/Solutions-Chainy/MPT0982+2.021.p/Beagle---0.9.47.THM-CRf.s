%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 221 expanded)
%              Number of leaves         :   39 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 748 expanded)
%              Number of equality atoms :   58 ( 216 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_139,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_144,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_152,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_144])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_157,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_44])).

tff(c_72,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_72])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_81,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_441,plain,(
    ! [E_115,A_113,B_114,F_116,D_118,C_117] :
      ( k1_partfun1(A_113,B_114,C_117,D_118,E_115,F_116) = k5_relat_1(E_115,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_117,D_118)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_449,plain,(
    ! [A_113,B_114,E_115] :
      ( k1_partfun1(A_113,B_114,'#skF_2','#skF_3',E_115,'#skF_5') = k5_relat_1(E_115,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_52,c_441])).

tff(c_663,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_2','#skF_3',E_127,'#skF_5') = k5_relat_1(E_127,'#skF_5')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_449])).

tff(c_684,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_663])).

tff(c_695,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_684])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_700,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_50])).

tff(c_278,plain,(
    ! [C_103,B_99,F_101,A_100,D_98,E_102] :
      ( k4_relset_1(A_100,B_99,C_103,D_98,E_102,F_101) = k5_relat_1(E_102,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_103,D_98)))
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_332,plain,(
    ! [A_110,B_111,E_112] :
      ( k4_relset_1(A_110,B_111,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_52,c_278])).

tff(c_344,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_332])).

tff(c_22,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( m1_subset_1(k4_relset_1(A_17,B_18,C_19,D_20,E_21,F_22),k1_zfmisc_1(k2_zfmisc_1(A_17,D_20)))
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_396,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_22])).

tff(c_400,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_396])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_436,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_400,c_26])).

tff(c_705,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_436])).

tff(c_79,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_48,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_126,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_183,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_192,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_133,c_186])).

tff(c_193,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_192])).

tff(c_244,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_relat_1(A_93),k2_relat_1(B_94))
      | ~ v2_funct_1(A_93)
      | k2_relat_1(k5_relat_1(B_94,A_93)) != k2_relat_1(A_93)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_255,plain,(
    ! [B_94] :
      ( r1_tarski('#skF_2',k2_relat_1(B_94))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_94,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_244])).

tff(c_262,plain,(
    ! [B_95] :
      ( r1_tarski('#skF_2',k2_relat_1(B_95))
      | k2_relat_1(k5_relat_1(B_95,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_56,c_48,c_255])).

tff(c_90,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k2_relat_1(B_54),A_55)
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(B_54) = A_55
      | ~ r1_tarski(A_55,k2_relat_1(B_54))
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_268,plain,(
    ! [B_95] :
      ( k2_relat_1(B_95) = '#skF_2'
      | ~ v5_relat_1(B_95,'#skF_2')
      | k2_relat_1(k5_relat_1(B_95,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_262,c_93])).

tff(c_718,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | k2_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_268])).

tff(c_762,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_62,c_89,c_718])).

tff(c_763,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_762])).

tff(c_88,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(B_71) = A_72
      | ~ r1_tarski(A_72,k2_relat_1(B_71))
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_174,plain,(
    ! [A_5,B_7] :
      ( k2_relat_1(k5_relat_1(A_5,B_7)) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_7,k2_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_162])).

tff(c_735,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_174])).

tff(c_775,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_88,c_705,c_735])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:37:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.52  
% 3.33/1.52  %Foreground sorts:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Background operators:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Foreground operators:
% 3.33/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.33/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.33/1.52  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.33/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.52  
% 3.33/1.54  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.33/1.54  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.33/1.54  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.54  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.54  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.33/1.54  tff(f_89, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.33/1.54  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.33/1.54  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.33/1.54  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.33/1.54  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 3.33/1.54  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.33/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.33/1.54  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.33/1.54  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_144, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.33/1.54  tff(c_152, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_144])).
% 3.33/1.54  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_157, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_44])).
% 3.33/1.54  tff(c_72, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.54  tff(c_80, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_72])).
% 3.33/1.54  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_81, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.54  tff(c_89, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_81])).
% 3.33/1.54  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_441, plain, (![E_115, A_113, B_114, F_116, D_118, C_117]: (k1_partfun1(A_113, B_114, C_117, D_118, E_115, F_116)=k5_relat_1(E_115, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_117, D_118))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.54  tff(c_449, plain, (![A_113, B_114, E_115]: (k1_partfun1(A_113, B_114, '#skF_2', '#skF_3', E_115, '#skF_5')=k5_relat_1(E_115, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_52, c_441])).
% 3.33/1.54  tff(c_663, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_2', '#skF_3', E_127, '#skF_5')=k5_relat_1(E_127, '#skF_5') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_449])).
% 3.33/1.54  tff(c_684, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_663])).
% 3.33/1.54  tff(c_695, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_684])).
% 3.33/1.54  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_700, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_695, c_50])).
% 3.33/1.54  tff(c_278, plain, (![C_103, B_99, F_101, A_100, D_98, E_102]: (k4_relset_1(A_100, B_99, C_103, D_98, E_102, F_101)=k5_relat_1(E_102, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_103, D_98))) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.54  tff(c_332, plain, (![A_110, B_111, E_112]: (k4_relset_1(A_110, B_111, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_52, c_278])).
% 3.33/1.54  tff(c_344, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_332])).
% 3.33/1.54  tff(c_22, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (m1_subset_1(k4_relset_1(A_17, B_18, C_19, D_20, E_21, F_22), k1_zfmisc_1(k2_zfmisc_1(A_17, D_20))) | ~m1_subset_1(F_22, k1_zfmisc_1(k2_zfmisc_1(C_19, D_20))) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.54  tff(c_396, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_344, c_22])).
% 3.33/1.54  tff(c_400, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_396])).
% 3.33/1.54  tff(c_26, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.33/1.54  tff(c_436, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_400, c_26])).
% 3.33/1.54  tff(c_705, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_700, c_436])).
% 3.33/1.54  tff(c_79, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_72])).
% 3.33/1.54  tff(c_48, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.33/1.54  tff(c_126, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.33/1.54  tff(c_133, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_126])).
% 3.33/1.54  tff(c_183, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.54  tff(c_186, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_183])).
% 3.33/1.54  tff(c_192, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_133, c_186])).
% 3.33/1.54  tff(c_193, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_192])).
% 3.33/1.54  tff(c_244, plain, (![A_93, B_94]: (r1_tarski(k1_relat_1(A_93), k2_relat_1(B_94)) | ~v2_funct_1(A_93) | k2_relat_1(k5_relat_1(B_94, A_93))!=k2_relat_1(A_93) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.33/1.54  tff(c_255, plain, (![B_94]: (r1_tarski('#skF_2', k2_relat_1(B_94)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_94, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_244])).
% 3.33/1.54  tff(c_262, plain, (![B_95]: (r1_tarski('#skF_2', k2_relat_1(B_95)) | k2_relat_1(k5_relat_1(B_95, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_56, c_48, c_255])).
% 3.33/1.54  tff(c_90, plain, (![B_54, A_55]: (r1_tarski(k2_relat_1(B_54), A_55) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.54  tff(c_93, plain, (![B_54, A_55]: (k2_relat_1(B_54)=A_55 | ~r1_tarski(A_55, k2_relat_1(B_54)) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_90, c_2])).
% 3.33/1.54  tff(c_268, plain, (![B_95]: (k2_relat_1(B_95)='#skF_2' | ~v5_relat_1(B_95, '#skF_2') | k2_relat_1(k5_relat_1(B_95, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_262, c_93])).
% 3.33/1.54  tff(c_718, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | k2_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_705, c_268])).
% 3.33/1.54  tff(c_762, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_62, c_89, c_718])).
% 3.33/1.54  tff(c_763, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_157, c_762])).
% 3.33/1.54  tff(c_88, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_81])).
% 3.33/1.54  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.54  tff(c_162, plain, (![B_71, A_72]: (k2_relat_1(B_71)=A_72 | ~r1_tarski(A_72, k2_relat_1(B_71)) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_90, c_2])).
% 3.33/1.54  tff(c_174, plain, (![A_5, B_7]: (k2_relat_1(k5_relat_1(A_5, B_7))=k2_relat_1(B_7) | ~v5_relat_1(B_7, k2_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_162])).
% 3.33/1.54  tff(c_735, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_705, c_174])).
% 3.33/1.54  tff(c_775, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_88, c_705, c_735])).
% 3.33/1.54  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_763, c_775])).
% 3.33/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  Inference rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Ref     : 0
% 3.33/1.54  #Sup     : 186
% 3.33/1.54  #Fact    : 0
% 3.33/1.54  #Define  : 0
% 3.33/1.54  #Split   : 4
% 3.33/1.54  #Chain   : 0
% 3.33/1.54  #Close   : 0
% 3.33/1.54  
% 3.33/1.54  Ordering : KBO
% 3.33/1.54  
% 3.33/1.54  Simplification rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Subsume      : 3
% 3.33/1.54  #Demod        : 66
% 3.33/1.54  #Tautology    : 62
% 3.33/1.54  #SimpNegUnit  : 10
% 3.33/1.54  #BackRed      : 5
% 3.33/1.54  
% 3.33/1.54  #Partial instantiations: 0
% 3.33/1.54  #Strategies tried      : 1
% 3.33/1.54  
% 3.33/1.54  Timing (in seconds)
% 3.33/1.54  ----------------------
% 3.33/1.55  Preprocessing        : 0.36
% 3.33/1.55  Parsing              : 0.20
% 3.33/1.55  CNF conversion       : 0.02
% 3.33/1.55  Main loop            : 0.38
% 3.33/1.55  Inferencing          : 0.13
% 3.33/1.55  Reduction            : 0.12
% 3.33/1.55  Demodulation         : 0.08
% 3.33/1.55  BG Simplification    : 0.02
% 3.33/1.55  Subsumption          : 0.07
% 3.33/1.55  Abstraction          : 0.02
% 3.33/1.55  MUC search           : 0.00
% 3.33/1.55  Cooper               : 0.00
% 3.33/1.55  Total                : 0.78
% 3.33/1.55  Index Insertion      : 0.00
% 3.33/1.55  Index Deletion       : 0.00
% 3.33/1.55  Index Matching       : 0.00
% 3.33/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
