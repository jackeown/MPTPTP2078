%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 9.74s
% Output     : CNFRefutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 407 expanded)
%              Number of leaves         :   43 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  275 (1321 expanded)
%              Number of equality atoms :   82 ( 377 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_180,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
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

tff(f_158,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_78,axiom,(
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

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_97,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_97])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_97])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_295,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_308,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_295])).

tff(c_429,plain,(
    ! [A_119,B_120,C_121] :
      ( m1_subset_1(k2_relset_1(A_119,B_120,C_121),k1_zfmisc_1(B_120))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_455,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_429])).

tff(c_469,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_455])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_475,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_469,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_478,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_475,c_2])).

tff(c_499,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_383,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_400,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_383])).

tff(c_4286,plain,(
    ! [B_431,A_432,C_433] :
      ( k1_xboole_0 = B_431
      | k1_relset_1(A_432,B_431,C_433) = A_432
      | ~ v1_funct_2(C_433,A_432,B_431)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_432,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4310,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4286])).

tff(c_4323,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_400,c_4310])).

tff(c_4324,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4323])).

tff(c_56,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_61),k2_relat_1(A_61))))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4362,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4324,c_56])).

tff(c_4391,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_4362])).

tff(c_318,plain,(
    ! [A_107] :
      ( m1_subset_1(A_107,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_107),k2_relat_1(A_107))))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_341,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,k2_zfmisc_1(k1_relat_1(A_107),k2_relat_1(A_107)))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_318,c_8])).

tff(c_4353,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4324,c_341])).

tff(c_4385,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_4353])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4754,plain,(
    ! [B_442,D_441,A_443,F_444,E_440,C_445] :
      ( k4_relset_1(A_443,B_442,C_445,D_441,E_440,F_444) = k5_relat_1(E_440,F_444)
      | ~ m1_subset_1(F_444,k1_zfmisc_1(k2_zfmisc_1(C_445,D_441)))
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(A_443,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6718,plain,(
    ! [D_539,A_536,A_538,C_537,E_535,B_534] :
      ( k4_relset_1(A_538,B_534,C_537,D_539,E_535,A_536) = k5_relat_1(E_535,A_536)
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(A_538,B_534)))
      | ~ r1_tarski(A_536,k2_zfmisc_1(C_537,D_539)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4754])).

tff(c_8036,plain,(
    ! [C_578,D_579,A_580] :
      ( k4_relset_1('#skF_1','#skF_2',C_578,D_579,'#skF_4',A_580) = k5_relat_1('#skF_4',A_580)
      | ~ r1_tarski(A_580,k2_zfmisc_1(C_578,D_579)) ) ),
    inference(resolution,[status(thm)],[c_76,c_6718])).

tff(c_8101,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2',k2_relat_1('#skF_5'),'#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4385,c_8036])).

tff(c_4836,plain,(
    ! [C_454,F_453,B_451,A_452,E_455,D_450] :
      ( m1_subset_1(k4_relset_1(A_452,B_451,C_454,D_450,E_455,F_453),k1_zfmisc_1(k2_zfmisc_1(A_452,D_450)))
      | ~ m1_subset_1(F_453,k1_zfmisc_1(k2_zfmisc_1(C_454,D_450)))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_452,B_451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4899,plain,(
    ! [C_454,F_453,B_451,A_452,E_455,D_450] :
      ( r1_tarski(k4_relset_1(A_452,B_451,C_454,D_450,E_455,F_453),k2_zfmisc_1(A_452,D_450))
      | ~ m1_subset_1(F_453,k1_zfmisc_1(k2_zfmisc_1(C_454,D_450)))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_452,B_451))) ) ),
    inference(resolution,[status(thm)],[c_4836,c_8])).

tff(c_8115,plain,
    ( r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1',k2_relat_1('#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8101,c_4899])).

tff(c_8122,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1',k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4391,c_8115])).

tff(c_5035,plain,(
    ! [C_461,A_460,E_463,B_458,D_459,F_462] :
      ( k1_partfun1(A_460,B_458,C_461,D_459,E_463,F_462) = k5_relat_1(E_463,F_462)
      | ~ m1_subset_1(F_462,k1_zfmisc_1(k2_zfmisc_1(C_461,D_459)))
      | ~ v1_funct_1(F_462)
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(A_460,B_458)))
      | ~ v1_funct_1(E_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_5060,plain,(
    ! [A_460,B_458,E_463] :
      ( k1_partfun1(A_460,B_458,'#skF_2','#skF_3',E_463,'#skF_5') = k5_relat_1(E_463,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(A_460,B_458)))
      | ~ v1_funct_1(E_463) ) ),
    inference(resolution,[status(thm)],[c_70,c_5035])).

tff(c_6271,plain,(
    ! [A_511,B_512,E_513] :
      ( k1_partfun1(A_511,B_512,'#skF_2','#skF_3',E_513,'#skF_5') = k5_relat_1(E_513,'#skF_5')
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512)))
      | ~ v1_funct_1(E_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5060])).

tff(c_6313,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_6271])).

tff(c_6335,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6313])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1540,plain,(
    ! [E_223,C_228,B_225,F_227,D_224,A_226] :
      ( k4_relset_1(A_226,B_225,C_228,D_224,E_223,F_227) = k5_relat_1(E_223,F_227)
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_228,D_224)))
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2070,plain,(
    ! [A_247,B_248,E_249] :
      ( k4_relset_1(A_247,B_248,'#skF_2','#skF_3',E_249,'#skF_5') = k5_relat_1(E_249,'#skF_5')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(resolution,[status(thm)],[c_70,c_1540])).

tff(c_2116,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_2070])).

tff(c_30,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k4_relset_1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2192,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_30])).

tff(c_2196,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_2192])).

tff(c_2256,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2196,c_8])).

tff(c_1866,plain,(
    ! [E_244,A_241,C_242,F_243,B_239,D_240] :
      ( k1_partfun1(A_241,B_239,C_242,D_240,E_244,F_243) = k5_relat_1(E_244,F_243)
      | ~ m1_subset_1(F_243,k1_zfmisc_1(k2_zfmisc_1(C_242,D_240)))
      | ~ v1_funct_1(F_243)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_1(E_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1889,plain,(
    ! [A_241,B_239,E_244] :
      ( k1_partfun1(A_241,B_239,'#skF_2','#skF_3',E_244,'#skF_5') = k5_relat_1(E_244,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_1(E_244) ) ),
    inference(resolution,[status(thm)],[c_70,c_1866])).

tff(c_3309,plain,(
    ! [A_312,B_313,E_314] :
      ( k1_partfun1(A_312,B_313,'#skF_2','#skF_3',E_314,'#skF_5') = k5_relat_1(E_314,'#skF_5')
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(E_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1889])).

tff(c_3351,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3309])).

tff(c_3373,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3351])).

tff(c_461,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_429])).

tff(c_512,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_678,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_512])).

tff(c_3377,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3373,c_678])).

tff(c_3382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_3377])).

tff(c_3384,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_36,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3415,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3384,c_36])).

tff(c_3430,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3415])).

tff(c_6349,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6335,c_3430])).

tff(c_306,plain,(
    ! [A_104,B_105,A_3] :
      ( k2_relset_1(A_104,B_105,A_3) = k2_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_10,c_295])).

tff(c_8145,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_5'),k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8122,c_306])).

tff(c_8164,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_5'),k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6349,c_8145])).

tff(c_3577,plain,(
    ! [A_326,B_327,C_328] :
      ( r1_tarski(k2_relset_1(A_326,B_327,C_328),B_327)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(resolution,[status(thm)],[c_429,c_8])).

tff(c_3600,plain,(
    ! [A_326,B_327,A_3] :
      ( r1_tarski(k2_relset_1(A_326,B_327,A_3),B_327)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_326,B_327)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3577])).

tff(c_8174,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1',k2_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8164,c_3600])).

tff(c_8181,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8122,c_8174])).

tff(c_8183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_8181])).

tff(c_8184,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_66,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_8812,plain,(
    ! [B_640,A_641,C_642] :
      ( k1_xboole_0 = B_640
      | k1_relset_1(A_641,B_640,C_642) = A_641
      | ~ v1_funct_2(C_642,A_641,B_640)
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(A_641,B_640))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8836,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8812])).

tff(c_8850,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_400,c_8836])).

tff(c_8851,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8850])).

tff(c_9145,plain,(
    ! [A_648,B_649] :
      ( r1_tarski(k1_relat_1(A_648),k2_relat_1(B_649))
      | ~ v2_funct_1(A_648)
      | k2_relat_1(k5_relat_1(B_649,A_648)) != k2_relat_1(A_648)
      | ~ v1_funct_1(B_649)
      | ~ v1_relat_1(B_649)
      | ~ v1_funct_1(A_648)
      | ~ v1_relat_1(A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9159,plain,(
    ! [B_649] :
      ( r1_tarski('#skF_2',k2_relat_1(B_649))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_649,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_649)
      | ~ v1_relat_1(B_649)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8851,c_9145])).

tff(c_9196,plain,(
    ! [B_651] :
      ( r1_tarski('#skF_2',k2_relat_1(B_651))
      | k2_relat_1(k5_relat_1(B_651,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_651)
      | ~ v1_relat_1(B_651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_8184,c_66,c_9159])).

tff(c_307,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_295])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_309,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_62])).

tff(c_458,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_429])).

tff(c_471,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_458])).

tff(c_482,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_471,c_8])).

tff(c_484,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_482,c_2])).

tff(c_487,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_484])).

tff(c_9205,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9196,c_487])).

tff(c_9220,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_80,c_9205])).

tff(c_9611,plain,(
    ! [C_674,E_676,D_672,F_675,B_671,A_673] :
      ( k1_partfun1(A_673,B_671,C_674,D_672,E_676,F_675) = k5_relat_1(E_676,F_675)
      | ~ m1_subset_1(F_675,k1_zfmisc_1(k2_zfmisc_1(C_674,D_672)))
      | ~ v1_funct_1(F_675)
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(A_673,B_671)))
      | ~ v1_funct_1(E_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_9634,plain,(
    ! [A_673,B_671,E_676] :
      ( k1_partfun1(A_673,B_671,'#skF_2','#skF_3',E_676,'#skF_5') = k5_relat_1(E_676,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(A_673,B_671)))
      | ~ v1_funct_1(E_676) ) ),
    inference(resolution,[status(thm)],[c_70,c_9611])).

tff(c_11636,plain,(
    ! [A_777,B_778,E_779] :
      ( k1_partfun1(A_777,B_778,'#skF_2','#skF_3',E_779,'#skF_5') = k5_relat_1(E_779,'#skF_5')
      | ~ m1_subset_1(E_779,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778)))
      | ~ v1_funct_1(E_779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9634])).

tff(c_11687,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_11636])).

tff(c_11710,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11687])).

tff(c_11726,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11710,c_68])).

tff(c_9249,plain,(
    ! [A_656,C_658,B_655,D_654,E_653,F_657] :
      ( k4_relset_1(A_656,B_655,C_658,D_654,E_653,F_657) = k5_relat_1(E_653,F_657)
      | ~ m1_subset_1(F_657,k1_zfmisc_1(k2_zfmisc_1(C_658,D_654)))
      | ~ m1_subset_1(E_653,k1_zfmisc_1(k2_zfmisc_1(A_656,B_655))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_9490,plain,(
    ! [A_668,B_669,E_670] :
      ( k4_relset_1(A_668,B_669,'#skF_2','#skF_3',E_670,'#skF_5') = k5_relat_1(E_670,'#skF_5')
      | ~ m1_subset_1(E_670,k1_zfmisc_1(k2_zfmisc_1(A_668,B_669))) ) ),
    inference(resolution,[status(thm)],[c_70,c_9249])).

tff(c_9528,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_9490])).

tff(c_9832,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9528,c_30])).

tff(c_9836,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_9832])).

tff(c_9889,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_9836,c_36])).

tff(c_11731,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11726,c_9889])).

tff(c_11733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9220,c_11731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.74/3.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.92  
% 9.74/3.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.74/3.93  
% 9.74/3.93  %Foreground sorts:
% 9.74/3.93  
% 9.74/3.93  
% 9.74/3.93  %Background operators:
% 9.74/3.93  
% 9.74/3.93  
% 9.74/3.93  %Foreground operators:
% 9.74/3.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.74/3.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.74/3.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.74/3.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.74/3.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.74/3.93  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 9.74/3.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.74/3.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.74/3.93  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.74/3.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.74/3.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.74/3.93  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.74/3.93  tff('#skF_5', type, '#skF_5': $i).
% 9.74/3.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.74/3.93  tff('#skF_2', type, '#skF_2': $i).
% 9.74/3.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.74/3.93  tff('#skF_3', type, '#skF_3': $i).
% 9.74/3.93  tff('#skF_1', type, '#skF_1': $i).
% 9.74/3.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.74/3.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.74/3.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.74/3.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.74/3.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.74/3.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.74/3.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.74/3.93  tff('#skF_4', type, '#skF_4': $i).
% 9.74/3.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.74/3.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.74/3.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.74/3.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.74/3.93  
% 10.02/3.95  tff(f_180, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 10.02/3.95  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.02/3.95  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.02/3.95  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 10.02/3.95  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.02/3.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.02/3.95  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.02/3.95  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.02/3.95  tff(f_158, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.02/3.95  tff(f_116, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 10.02/3.95  tff(f_98, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 10.02/3.95  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.02/3.95  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 10.02/3.95  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_97, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.02/3.95  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_97])).
% 10.02/3.95  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_97])).
% 10.02/3.95  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_295, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.02/3.95  tff(c_308, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_295])).
% 10.02/3.95  tff(c_429, plain, (![A_119, B_120, C_121]: (m1_subset_1(k2_relset_1(A_119, B_120, C_121), k1_zfmisc_1(B_120)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.02/3.95  tff(c_455, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_308, c_429])).
% 10.02/3.95  tff(c_469, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_455])).
% 10.02/3.95  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/3.95  tff(c_475, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_469, c_8])).
% 10.02/3.95  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/3.95  tff(c_478, plain, (k2_relat_1('#skF_5')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_475, c_2])).
% 10.02/3.95  tff(c_499, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_478])).
% 10.02/3.95  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_383, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.02/3.95  tff(c_400, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_383])).
% 10.02/3.95  tff(c_4286, plain, (![B_431, A_432, C_433]: (k1_xboole_0=B_431 | k1_relset_1(A_432, B_431, C_433)=A_432 | ~v1_funct_2(C_433, A_432, B_431) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_432, B_431))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.02/3.95  tff(c_4310, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_4286])).
% 10.02/3.95  tff(c_4323, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_400, c_4310])).
% 10.02/3.95  tff(c_4324, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_4323])).
% 10.02/3.95  tff(c_56, plain, (![A_61]: (m1_subset_1(A_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_61), k2_relat_1(A_61)))) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.02/3.95  tff(c_4362, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4324, c_56])).
% 10.02/3.95  tff(c_4391, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_4362])).
% 10.02/3.95  tff(c_318, plain, (![A_107]: (m1_subset_1(A_107, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_107), k2_relat_1(A_107)))) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.02/3.95  tff(c_341, plain, (![A_107]: (r1_tarski(A_107, k2_zfmisc_1(k1_relat_1(A_107), k2_relat_1(A_107))) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_318, c_8])).
% 10.02/3.95  tff(c_4353, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4324, c_341])).
% 10.02/3.95  tff(c_4385, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_4353])).
% 10.02/3.95  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.02/3.95  tff(c_4754, plain, (![B_442, D_441, A_443, F_444, E_440, C_445]: (k4_relset_1(A_443, B_442, C_445, D_441, E_440, F_444)=k5_relat_1(E_440, F_444) | ~m1_subset_1(F_444, k1_zfmisc_1(k2_zfmisc_1(C_445, D_441))) | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(A_443, B_442))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.02/3.95  tff(c_6718, plain, (![D_539, A_536, A_538, C_537, E_535, B_534]: (k4_relset_1(A_538, B_534, C_537, D_539, E_535, A_536)=k5_relat_1(E_535, A_536) | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(A_538, B_534))) | ~r1_tarski(A_536, k2_zfmisc_1(C_537, D_539)))), inference(resolution, [status(thm)], [c_10, c_4754])).
% 10.02/3.95  tff(c_8036, plain, (![C_578, D_579, A_580]: (k4_relset_1('#skF_1', '#skF_2', C_578, D_579, '#skF_4', A_580)=k5_relat_1('#skF_4', A_580) | ~r1_tarski(A_580, k2_zfmisc_1(C_578, D_579)))), inference(resolution, [status(thm)], [c_76, c_6718])).
% 10.02/3.95  tff(c_8101, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', k2_relat_1('#skF_5'), '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4385, c_8036])).
% 10.02/3.95  tff(c_4836, plain, (![C_454, F_453, B_451, A_452, E_455, D_450]: (m1_subset_1(k4_relset_1(A_452, B_451, C_454, D_450, E_455, F_453), k1_zfmisc_1(k2_zfmisc_1(A_452, D_450))) | ~m1_subset_1(F_453, k1_zfmisc_1(k2_zfmisc_1(C_454, D_450))) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_452, B_451))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.02/3.95  tff(c_4899, plain, (![C_454, F_453, B_451, A_452, E_455, D_450]: (r1_tarski(k4_relset_1(A_452, B_451, C_454, D_450, E_455, F_453), k2_zfmisc_1(A_452, D_450)) | ~m1_subset_1(F_453, k1_zfmisc_1(k2_zfmisc_1(C_454, D_450))) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_452, B_451))))), inference(resolution, [status(thm)], [c_4836, c_8])).
% 10.02/3.95  tff(c_8115, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', k2_relat_1('#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8101, c_4899])).
% 10.02/3.95  tff(c_8122, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4391, c_8115])).
% 10.02/3.95  tff(c_5035, plain, (![C_461, A_460, E_463, B_458, D_459, F_462]: (k1_partfun1(A_460, B_458, C_461, D_459, E_463, F_462)=k5_relat_1(E_463, F_462) | ~m1_subset_1(F_462, k1_zfmisc_1(k2_zfmisc_1(C_461, D_459))) | ~v1_funct_1(F_462) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(A_460, B_458))) | ~v1_funct_1(E_463))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.02/3.95  tff(c_5060, plain, (![A_460, B_458, E_463]: (k1_partfun1(A_460, B_458, '#skF_2', '#skF_3', E_463, '#skF_5')=k5_relat_1(E_463, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(A_460, B_458))) | ~v1_funct_1(E_463))), inference(resolution, [status(thm)], [c_70, c_5035])).
% 10.02/3.95  tff(c_6271, plain, (![A_511, B_512, E_513]: (k1_partfun1(A_511, B_512, '#skF_2', '#skF_3', E_513, '#skF_5')=k5_relat_1(E_513, '#skF_5') | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))) | ~v1_funct_1(E_513))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5060])).
% 10.02/3.95  tff(c_6313, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_6271])).
% 10.02/3.95  tff(c_6335, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6313])).
% 10.02/3.95  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_1540, plain, (![E_223, C_228, B_225, F_227, D_224, A_226]: (k4_relset_1(A_226, B_225, C_228, D_224, E_223, F_227)=k5_relat_1(E_223, F_227) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_228, D_224))) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.02/3.95  tff(c_2070, plain, (![A_247, B_248, E_249]: (k4_relset_1(A_247, B_248, '#skF_2', '#skF_3', E_249, '#skF_5')=k5_relat_1(E_249, '#skF_5') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(resolution, [status(thm)], [c_70, c_1540])).
% 10.02/3.95  tff(c_2116, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_2070])).
% 10.02/3.95  tff(c_30, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k4_relset_1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.02/3.95  tff(c_2192, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_30])).
% 10.02/3.95  tff(c_2196, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_2192])).
% 10.02/3.95  tff(c_2256, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_2196, c_8])).
% 10.02/3.95  tff(c_1866, plain, (![E_244, A_241, C_242, F_243, B_239, D_240]: (k1_partfun1(A_241, B_239, C_242, D_240, E_244, F_243)=k5_relat_1(E_244, F_243) | ~m1_subset_1(F_243, k1_zfmisc_1(k2_zfmisc_1(C_242, D_240))) | ~v1_funct_1(F_243) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_1(E_244))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.02/3.95  tff(c_1889, plain, (![A_241, B_239, E_244]: (k1_partfun1(A_241, B_239, '#skF_2', '#skF_3', E_244, '#skF_5')=k5_relat_1(E_244, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_1(E_244))), inference(resolution, [status(thm)], [c_70, c_1866])).
% 10.02/3.95  tff(c_3309, plain, (![A_312, B_313, E_314]: (k1_partfun1(A_312, B_313, '#skF_2', '#skF_3', E_314, '#skF_5')=k5_relat_1(E_314, '#skF_5') | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_1(E_314))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1889])).
% 10.02/3.95  tff(c_3351, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3309])).
% 10.02/3.95  tff(c_3373, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3351])).
% 10.02/3.95  tff(c_461, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_429])).
% 10.02/3.95  tff(c_512, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_461])).
% 10.02/3.95  tff(c_678, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_512])).
% 10.02/3.95  tff(c_3377, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3373, c_678])).
% 10.02/3.95  tff(c_3382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2256, c_3377])).
% 10.02/3.95  tff(c_3384, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_461])).
% 10.02/3.95  tff(c_36, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.02/3.95  tff(c_3415, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_3384, c_36])).
% 10.02/3.95  tff(c_3430, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3415])).
% 10.02/3.95  tff(c_6349, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6335, c_3430])).
% 10.02/3.95  tff(c_306, plain, (![A_104, B_105, A_3]: (k2_relset_1(A_104, B_105, A_3)=k2_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_10, c_295])).
% 10.02/3.95  tff(c_8145, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_5'), k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_8122, c_306])).
% 10.02/3.95  tff(c_8164, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_5'), k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6349, c_8145])).
% 10.02/3.95  tff(c_3577, plain, (![A_326, B_327, C_328]: (r1_tarski(k2_relset_1(A_326, B_327, C_328), B_327) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(resolution, [status(thm)], [c_429, c_8])).
% 10.02/3.95  tff(c_3600, plain, (![A_326, B_327, A_3]: (r1_tarski(k2_relset_1(A_326, B_327, A_3), B_327) | ~r1_tarski(A_3, k2_zfmisc_1(A_326, B_327)))), inference(resolution, [status(thm)], [c_10, c_3577])).
% 10.02/3.95  tff(c_8174, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', k2_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8164, c_3600])).
% 10.02/3.95  tff(c_8181, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8122, c_8174])).
% 10.02/3.95  tff(c_8183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_8181])).
% 10.02/3.95  tff(c_8184, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_478])).
% 10.02/3.95  tff(c_66, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_8812, plain, (![B_640, A_641, C_642]: (k1_xboole_0=B_640 | k1_relset_1(A_641, B_640, C_642)=A_641 | ~v1_funct_2(C_642, A_641, B_640) | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(A_641, B_640))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.02/3.95  tff(c_8836, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_8812])).
% 10.02/3.95  tff(c_8850, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_400, c_8836])).
% 10.02/3.95  tff(c_8851, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_8850])).
% 10.02/3.95  tff(c_9145, plain, (![A_648, B_649]: (r1_tarski(k1_relat_1(A_648), k2_relat_1(B_649)) | ~v2_funct_1(A_648) | k2_relat_1(k5_relat_1(B_649, A_648))!=k2_relat_1(A_648) | ~v1_funct_1(B_649) | ~v1_relat_1(B_649) | ~v1_funct_1(A_648) | ~v1_relat_1(A_648))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.02/3.95  tff(c_9159, plain, (![B_649]: (r1_tarski('#skF_2', k2_relat_1(B_649)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_649, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_649) | ~v1_relat_1(B_649) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8851, c_9145])).
% 10.02/3.95  tff(c_9196, plain, (![B_651]: (r1_tarski('#skF_2', k2_relat_1(B_651)) | k2_relat_1(k5_relat_1(B_651, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_651) | ~v1_relat_1(B_651))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_8184, c_66, c_9159])).
% 10.02/3.95  tff(c_307, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_295])).
% 10.02/3.95  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.02/3.95  tff(c_309, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_62])).
% 10.02/3.95  tff(c_458, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_429])).
% 10.02/3.95  tff(c_471, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_458])).
% 10.02/3.95  tff(c_482, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_471, c_8])).
% 10.02/3.95  tff(c_484, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_482, c_2])).
% 10.02/3.95  tff(c_487, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_309, c_484])).
% 10.02/3.95  tff(c_9205, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9196, c_487])).
% 10.02/3.95  tff(c_9220, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_80, c_9205])).
% 10.02/3.95  tff(c_9611, plain, (![C_674, E_676, D_672, F_675, B_671, A_673]: (k1_partfun1(A_673, B_671, C_674, D_672, E_676, F_675)=k5_relat_1(E_676, F_675) | ~m1_subset_1(F_675, k1_zfmisc_1(k2_zfmisc_1(C_674, D_672))) | ~v1_funct_1(F_675) | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(A_673, B_671))) | ~v1_funct_1(E_676))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.02/3.95  tff(c_9634, plain, (![A_673, B_671, E_676]: (k1_partfun1(A_673, B_671, '#skF_2', '#skF_3', E_676, '#skF_5')=k5_relat_1(E_676, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(A_673, B_671))) | ~v1_funct_1(E_676))), inference(resolution, [status(thm)], [c_70, c_9611])).
% 10.02/3.95  tff(c_11636, plain, (![A_777, B_778, E_779]: (k1_partfun1(A_777, B_778, '#skF_2', '#skF_3', E_779, '#skF_5')=k5_relat_1(E_779, '#skF_5') | ~m1_subset_1(E_779, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))) | ~v1_funct_1(E_779))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9634])).
% 10.02/3.95  tff(c_11687, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_11636])).
% 10.02/3.95  tff(c_11710, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11687])).
% 10.02/3.95  tff(c_11726, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11710, c_68])).
% 10.02/3.95  tff(c_9249, plain, (![A_656, C_658, B_655, D_654, E_653, F_657]: (k4_relset_1(A_656, B_655, C_658, D_654, E_653, F_657)=k5_relat_1(E_653, F_657) | ~m1_subset_1(F_657, k1_zfmisc_1(k2_zfmisc_1(C_658, D_654))) | ~m1_subset_1(E_653, k1_zfmisc_1(k2_zfmisc_1(A_656, B_655))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.02/3.95  tff(c_9490, plain, (![A_668, B_669, E_670]: (k4_relset_1(A_668, B_669, '#skF_2', '#skF_3', E_670, '#skF_5')=k5_relat_1(E_670, '#skF_5') | ~m1_subset_1(E_670, k1_zfmisc_1(k2_zfmisc_1(A_668, B_669))))), inference(resolution, [status(thm)], [c_70, c_9249])).
% 10.02/3.95  tff(c_9528, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_9490])).
% 10.02/3.95  tff(c_9832, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_9528, c_30])).
% 10.02/3.95  tff(c_9836, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_9832])).
% 10.02/3.95  tff(c_9889, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_9836, c_36])).
% 10.02/3.95  tff(c_11731, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11726, c_9889])).
% 10.02/3.95  tff(c_11733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9220, c_11731])).
% 10.02/3.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/3.95  
% 10.02/3.95  Inference rules
% 10.02/3.95  ----------------------
% 10.02/3.95  #Ref     : 0
% 10.02/3.95  #Sup     : 2715
% 10.02/3.95  #Fact    : 0
% 10.02/3.95  #Define  : 0
% 10.02/3.95  #Split   : 36
% 10.02/3.95  #Chain   : 0
% 10.02/3.95  #Close   : 0
% 10.02/3.95  
% 10.02/3.95  Ordering : KBO
% 10.02/3.95  
% 10.02/3.95  Simplification rules
% 10.02/3.95  ----------------------
% 10.02/3.95  #Subsume      : 55
% 10.02/3.95  #Demod        : 1848
% 10.02/3.95  #Tautology    : 965
% 10.02/3.95  #SimpNegUnit  : 72
% 10.02/3.95  #BackRed      : 87
% 10.02/3.95  
% 10.02/3.95  #Partial instantiations: 0
% 10.02/3.95  #Strategies tried      : 1
% 10.02/3.95  
% 10.02/3.95  Timing (in seconds)
% 10.02/3.95  ----------------------
% 10.02/3.95  Preprocessing        : 0.39
% 10.02/3.95  Parsing              : 0.20
% 10.02/3.95  CNF conversion       : 0.03
% 10.02/3.95  Main loop            : 2.77
% 10.02/3.95  Inferencing          : 0.83
% 10.02/3.95  Reduction            : 1.14
% 10.02/3.96  Demodulation         : 0.85
% 10.02/3.96  BG Simplification    : 0.08
% 10.02/3.96  Subsumption          : 0.50
% 10.02/3.96  Abstraction          : 0.10
% 10.02/3.96  MUC search           : 0.00
% 10.02/3.96  Cooper               : 0.00
% 10.02/3.96  Total                : 3.21
% 10.02/3.96  Index Insertion      : 0.00
% 10.02/3.96  Index Deletion       : 0.00
% 10.02/3.96  Index Matching       : 0.00
% 10.02/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
