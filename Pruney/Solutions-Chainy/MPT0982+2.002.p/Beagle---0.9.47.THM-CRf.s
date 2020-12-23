%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 734 expanded)
%              Number of leaves         :   44 ( 285 expanded)
%              Depth                    :   20
%              Number of atoms          :  246 (2844 expanded)
%              Number of equality atoms :   57 ( 764 expanded)
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

tff(f_163,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_153,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_160,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_153])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_162,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_56])).

tff(c_86,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_86])).

tff(c_95,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_102,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_95])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_171,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_179,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_294,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_300,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_294])).

tff(c_306,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_179,c_300])).

tff(c_307,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_306])).

tff(c_210,plain,(
    ! [A_79] :
      ( k2_relat_1(k5_relat_1(A_79,k2_funct_1(A_79))) = k1_relat_1(A_79)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_373,plain,(
    ! [A_115] :
      ( r1_tarski(k1_relat_1(A_115),k2_relat_1(k2_funct_1(A_115)))
      | ~ v1_relat_1(k2_funct_1(A_115))
      | ~ v1_relat_1(A_115)
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_14])).

tff(c_384,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_373])).

tff(c_393,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_60,c_94,c_384])).

tff(c_394,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_397,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_394])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_397])).

tff(c_403,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_404,plain,(
    ! [A_116,D_121,C_120,F_119,E_118,B_117] :
      ( k1_partfun1(A_116,B_117,C_120,D_121,E_118,F_119) = k5_relat_1(E_118,F_119)
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_120,D_121)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_408,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(resolution,[status(thm)],[c_64,c_404])).

tff(c_652,plain,(
    ! [A_133,B_134,E_135] :
      ( k1_partfun1(A_133,B_134,'#skF_2','#skF_3',E_135,'#skF_5') = k5_relat_1(E_135,'#skF_5')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_408])).

tff(c_664,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_652])).

tff(c_677,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_664])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_682,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_62])).

tff(c_50,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_686,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_50])).

tff(c_690,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_686])).

tff(c_36,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_723,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_690,c_36])).

tff(c_759,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_723])).

tff(c_117,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_206,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_189])).

tff(c_784,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_206])).

tff(c_818,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94,c_103,c_759,c_784])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_853,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_12])).

tff(c_1009,plain,(
    ! [B_146] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_146)) = k9_relat_1(B_146,'#skF_3')
      | ~ v1_relat_1(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_853])).

tff(c_1062,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1009])).

tff(c_1076,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_60,c_403,c_307,c_1062])).

tff(c_249,plain,(
    ! [B_81,A_82] :
      ( k10_relat_1(k2_funct_1(B_81),A_82) = k9_relat_1(B_81,A_82)
      | ~ v2_funct_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,k10_relat_1(B_13,A_12)),A_12)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_763,plain,(
    ! [B_136,A_137] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_136),k9_relat_1(B_136,A_137)),A_137)
      | ~ v1_funct_1(k2_funct_1(B_136))
      | ~ v1_relat_1(k2_funct_1(B_136))
      | ~ v2_funct_1(B_136)
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_20])).

tff(c_3999,plain,(
    ! [B_294,A_295] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_294),k2_relat_1(k5_relat_1(A_295,B_294))),k2_relat_1(A_295))
      | ~ v1_funct_1(k2_funct_1(B_294))
      | ~ v1_relat_1(k2_funct_1(B_294))
      | ~ v2_funct_1(B_294)
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_763])).

tff(c_4028,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_5'),'#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_3999])).

tff(c_4050,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94,c_94,c_68,c_60,c_403,c_1076,c_4028])).

tff(c_4053,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4050])).

tff(c_4056,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_4053])).

tff(c_4060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_4056])).

tff(c_4061,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4050])).

tff(c_120,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(B_59) = A_60
      | ~ r1_tarski(A_60,k2_relat_1(B_59))
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_4071,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4061,c_120])).

tff(c_4076,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_102,c_4071])).

tff(c_4078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_4076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.61  
% 7.11/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.11/2.61  
% 7.11/2.61  %Foreground sorts:
% 7.11/2.61  
% 7.11/2.61  
% 7.11/2.61  %Background operators:
% 7.11/2.61  
% 7.11/2.61  
% 7.11/2.61  %Foreground operators:
% 7.11/2.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.11/2.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.11/2.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.11/2.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.11/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.11/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.11/2.61  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.11/2.61  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.11/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.61  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.11/2.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.11/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.11/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.11/2.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.11/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.11/2.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.11/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.61  
% 7.11/2.63  tff(f_163, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 7.11/2.63  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.11/2.63  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.11/2.63  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.11/2.63  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.11/2.63  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.11/2.63  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.11/2.63  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 7.11/2.63  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 7.11/2.63  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.11/2.63  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.11/2.63  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.11/2.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.11/2.63  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 7.11/2.63  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 7.11/2.63  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 7.11/2.63  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_153, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.63  tff(c_160, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_153])).
% 7.11/2.63  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_162, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_56])).
% 7.11/2.63  tff(c_86, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.11/2.63  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_86])).
% 7.11/2.63  tff(c_95, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.11/2.63  tff(c_102, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_95])).
% 7.11/2.63  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_86])).
% 7.11/2.63  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_16, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.11/2.63  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_18, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.11/2.63  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_171, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.11/2.63  tff(c_179, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_171])).
% 7.11/2.63  tff(c_294, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.11/2.63  tff(c_300, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_294])).
% 7.11/2.63  tff(c_306, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_179, c_300])).
% 7.11/2.63  tff(c_307, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_306])).
% 7.11/2.63  tff(c_210, plain, (![A_79]: (k2_relat_1(k5_relat_1(A_79, k2_funct_1(A_79)))=k1_relat_1(A_79) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.11/2.63  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.11/2.63  tff(c_373, plain, (![A_115]: (r1_tarski(k1_relat_1(A_115), k2_relat_1(k2_funct_1(A_115))) | ~v1_relat_1(k2_funct_1(A_115)) | ~v1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_210, c_14])).
% 7.11/2.63  tff(c_384, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_307, c_373])).
% 7.11/2.63  tff(c_393, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_60, c_94, c_384])).
% 7.11/2.63  tff(c_394, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_393])).
% 7.11/2.63  tff(c_397, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_394])).
% 7.11/2.63  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_397])).
% 7.11/2.63  tff(c_403, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_393])).
% 7.11/2.63  tff(c_24, plain, (![A_16]: (k2_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.11/2.63  tff(c_103, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_95])).
% 7.11/2.63  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_404, plain, (![A_116, D_121, C_120, F_119, E_118, B_117]: (k1_partfun1(A_116, B_117, C_120, D_121, E_118, F_119)=k5_relat_1(E_118, F_119) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_120, D_121))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.11/2.63  tff(c_408, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(resolution, [status(thm)], [c_64, c_404])).
% 7.11/2.63  tff(c_652, plain, (![A_133, B_134, E_135]: (k1_partfun1(A_133, B_134, '#skF_2', '#skF_3', E_135, '#skF_5')=k5_relat_1(E_135, '#skF_5') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(E_135))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_408])).
% 7.11/2.63  tff(c_664, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_652])).
% 7.11/2.63  tff(c_677, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_664])).
% 7.11/2.63  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.11/2.63  tff(c_682, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_62])).
% 7.11/2.63  tff(c_50, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.11/2.63  tff(c_686, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_677, c_50])).
% 7.11/2.63  tff(c_690, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_686])).
% 7.11/2.63  tff(c_36, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.63  tff(c_723, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_690, c_36])).
% 7.11/2.63  tff(c_759, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_723])).
% 7.11/2.63  tff(c_117, plain, (![B_59, A_60]: (r1_tarski(k2_relat_1(B_59), A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.11/2.63  tff(c_189, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_117, c_2])).
% 7.11/2.63  tff(c_206, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_189])).
% 7.11/2.63  tff(c_784, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_759, c_206])).
% 7.11/2.63  tff(c_818, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94, c_103, c_759, c_784])).
% 7.11/2.63  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.63  tff(c_853, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_12])).
% 7.11/2.63  tff(c_1009, plain, (![B_146]: (k2_relat_1(k5_relat_1('#skF_5', B_146))=k9_relat_1(B_146, '#skF_3') | ~v1_relat_1(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_853])).
% 7.11/2.63  tff(c_1062, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1009])).
% 7.11/2.63  tff(c_1076, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_60, c_403, c_307, c_1062])).
% 7.11/2.63  tff(c_249, plain, (![B_81, A_82]: (k10_relat_1(k2_funct_1(B_81), A_82)=k9_relat_1(B_81, A_82) | ~v2_funct_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.11/2.63  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, k10_relat_1(B_13, A_12)), A_12) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.11/2.63  tff(c_763, plain, (![B_136, A_137]: (r1_tarski(k9_relat_1(k2_funct_1(B_136), k9_relat_1(B_136, A_137)), A_137) | ~v1_funct_1(k2_funct_1(B_136)) | ~v1_relat_1(k2_funct_1(B_136)) | ~v2_funct_1(B_136) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_249, c_20])).
% 7.11/2.63  tff(c_3999, plain, (![B_294, A_295]: (r1_tarski(k9_relat_1(k2_funct_1(B_294), k2_relat_1(k5_relat_1(A_295, B_294))), k2_relat_1(A_295)) | ~v1_funct_1(k2_funct_1(B_294)) | ~v1_relat_1(k2_funct_1(B_294)) | ~v2_funct_1(B_294) | ~v1_funct_1(B_294) | ~v1_relat_1(B_294) | ~v1_relat_1(B_294) | ~v1_relat_1(A_295))), inference(superposition, [status(thm), theory('equality')], [c_12, c_763])).
% 7.11/2.63  tff(c_4028, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_5'), '#skF_3'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_759, c_3999])).
% 7.11/2.63  tff(c_4050, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94, c_94, c_68, c_60, c_403, c_1076, c_4028])).
% 7.11/2.63  tff(c_4053, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4050])).
% 7.11/2.63  tff(c_4056, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_4053])).
% 7.11/2.63  tff(c_4060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_4056])).
% 7.11/2.63  tff(c_4061, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4050])).
% 7.11/2.63  tff(c_120, plain, (![B_59, A_60]: (k2_relat_1(B_59)=A_60 | ~r1_tarski(A_60, k2_relat_1(B_59)) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_117, c_2])).
% 7.11/2.63  tff(c_4071, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4061, c_120])).
% 7.11/2.63  tff(c_4076, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_102, c_4071])).
% 7.11/2.63  tff(c_4078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_4076])).
% 7.11/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.63  
% 7.11/2.63  Inference rules
% 7.11/2.63  ----------------------
% 7.11/2.63  #Ref     : 0
% 7.11/2.63  #Sup     : 839
% 7.11/2.63  #Fact    : 0
% 7.11/2.63  #Define  : 0
% 7.11/2.63  #Split   : 16
% 7.11/2.63  #Chain   : 0
% 7.11/2.63  #Close   : 0
% 7.11/2.63  
% 7.11/2.63  Ordering : KBO
% 7.11/2.63  
% 7.11/2.63  Simplification rules
% 7.11/2.63  ----------------------
% 7.11/2.63  #Subsume      : 52
% 7.11/2.63  #Demod        : 1003
% 7.11/2.63  #Tautology    : 175
% 7.11/2.63  #SimpNegUnit  : 33
% 7.11/2.63  #BackRed      : 39
% 7.11/2.63  
% 7.11/2.63  #Partial instantiations: 0
% 7.11/2.63  #Strategies tried      : 1
% 7.11/2.63  
% 7.11/2.63  Timing (in seconds)
% 7.11/2.63  ----------------------
% 7.11/2.63  Preprocessing        : 0.35
% 7.11/2.63  Parsing              : 0.19
% 7.11/2.63  CNF conversion       : 0.02
% 7.11/2.63  Main loop            : 1.50
% 7.11/2.63  Inferencing          : 0.46
% 7.11/2.63  Reduction            : 0.62
% 7.11/2.63  Demodulation         : 0.46
% 7.11/2.63  BG Simplification    : 0.04
% 7.11/2.63  Subsumption          : 0.28
% 7.11/2.63  Abstraction          : 0.06
% 7.11/2.63  MUC search           : 0.00
% 7.11/2.63  Cooper               : 0.00
% 7.11/2.63  Total                : 1.89
% 7.11/2.63  Index Insertion      : 0.00
% 7.11/2.63  Index Deletion       : 0.00
% 7.11/2.63  Index Matching       : 0.00
% 7.11/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
