%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  144 (1746 expanded)
%              Number of leaves         :   32 ( 522 expanded)
%              Depth                    :   18
%              Number of atoms          :  278 (6767 expanded)
%              Number of equality atoms :   69 (2531 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_30,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_159,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k2_relset_1(A_52,B_53,C_54),k1_zfmisc_1(B_53))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_159])).

tff(c_186,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_177])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_120,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_308,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_308])).

tff(c_330,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_133,c_322])).

tff(c_331,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_330])).

tff(c_411,plain,(
    ! [B_93,A_94] :
      ( v2_funct_1(B_93)
      | ~ r1_tarski(k2_relat_1(B_93),k1_relat_1(A_94))
      | ~ v2_funct_1(k5_relat_1(B_93,A_94))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_417,plain,(
    ! [B_93] :
      ( v2_funct_1(B_93)
      | ~ r1_tarski(k2_relat_1(B_93),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_93,'#skF_5'))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_411])).

tff(c_423,plain,(
    ! [B_96] :
      ( v2_funct_1(B_96)
      | ~ r1_tarski(k2_relat_1(B_96),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_96,'#skF_5'))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_417])).

tff(c_426,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_423])).

tff(c_429,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46,c_426])).

tff(c_430,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_429])).

tff(c_431,plain,(
    ! [C_99,B_101,F_100,D_98,A_97,E_102] :
      ( k1_partfun1(A_97,B_101,C_99,D_98,E_102,F_100) = k5_relat_1(E_102,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_98)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_97,B_101)))
      | ~ v1_funct_1(E_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_441,plain,(
    ! [A_97,B_101,E_102] :
      ( k1_partfun1(A_97,B_101,'#skF_2','#skF_3',E_102,'#skF_5') = k5_relat_1(E_102,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_97,B_101)))
      | ~ v1_funct_1(E_102) ) ),
    inference(resolution,[status(thm)],[c_36,c_431])).

tff(c_499,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_3',E_111,'#skF_5') = k5_relat_1(E_111,'#skF_5')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441])).

tff(c_510,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_518,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_510])).

tff(c_34,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_522,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_34])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_522])).

tff(c_526,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_525,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_531,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_525])).

tff(c_543,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_42])).

tff(c_559,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_571,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_543,c_559])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_541,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_44])).

tff(c_18,plain,(
    ! [C_20,A_18] :
      ( k1_xboole_0 = C_20
      | ~ v1_funct_2(C_20,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_713,plain,(
    ! [C_142,A_143] :
      ( C_142 = '#skF_3'
      | ~ v1_funct_2(C_142,A_143,'#skF_3')
      | A_143 = '#skF_3'
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_526,c_526,c_526,c_18])).

tff(c_724,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_543,c_713])).

tff(c_732,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_724])).

tff(c_737,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_584,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_596,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_543,c_584])).

tff(c_657,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1(k2_relset_1(A_136,B_137,C_138),k1_zfmisc_1(B_137))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_678,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_657])).

tff(c_686,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_678])).

tff(c_694,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_686,c_2])).

tff(c_739,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_694])).

tff(c_542,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_36])).

tff(c_572,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_542,c_559])).

tff(c_540,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_38])).

tff(c_755,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_540])).

tff(c_617,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_630,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_542,c_617])).

tff(c_744,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_630])).

tff(c_753,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_542])).

tff(c_757,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_526])).

tff(c_24,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_897,plain,(
    ! [B_146,C_147] :
      ( k1_relset_1('#skF_1',B_146,C_147) = '#skF_1'
      | ~ v1_funct_2(C_147,'#skF_1',B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_146))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_757,c_757,c_757,c_24])).

tff(c_900,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_753,c_897])).

tff(c_914,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_744,c_900])).

tff(c_1096,plain,(
    ! [B_165,A_166] :
      ( v2_funct_1(B_165)
      | ~ r1_tarski(k2_relat_1(B_165),k1_relat_1(A_166))
      | ~ v2_funct_1(k5_relat_1(B_165,A_166))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1102,plain,(
    ! [B_165] :
      ( v2_funct_1(B_165)
      | ~ r1_tarski(k2_relat_1(B_165),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_165,'#skF_5'))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_1096])).

tff(c_1165,plain,(
    ! [B_180] :
      ( v2_funct_1(B_180)
      | ~ r1_tarski(k2_relat_1(B_180),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_180,'#skF_5'))
      | ~ v1_funct_1(B_180)
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_40,c_1102])).

tff(c_1171,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_739,c_1165])).

tff(c_1177,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_46,c_1171])).

tff(c_1178,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1177])).

tff(c_752,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_543])).

tff(c_1146,plain,(
    ! [C_176,A_174,B_178,F_177,D_175,E_179] :
      ( k1_partfun1(A_174,B_178,C_176,D_175,E_179,F_177) = k5_relat_1(E_179,F_177)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(C_176,D_175)))
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_174,B_178)))
      | ~ v1_funct_1(E_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1148,plain,(
    ! [A_174,B_178,E_179] :
      ( k1_partfun1(A_174,B_178,'#skF_1','#skF_1',E_179,'#skF_5') = k5_relat_1(E_179,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_174,B_178)))
      | ~ v1_funct_1(E_179) ) ),
    inference(resolution,[status(thm)],[c_753,c_1146])).

tff(c_1289,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_1','#skF_1',E_203,'#skF_5') = k5_relat_1(E_203,'#skF_5')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1148])).

tff(c_1295,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_752,c_1289])).

tff(c_1309,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1295])).

tff(c_558,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_531,c_34])).

tff(c_749,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_737,c_558])).

tff(c_1316,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_749])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1178,c_1316])).

tff(c_1319,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_1322,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_694])).

tff(c_1338,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_540])).

tff(c_1336,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_542])).

tff(c_1340,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_526])).

tff(c_1414,plain,(
    ! [B_206,C_207] :
      ( k1_relset_1('#skF_4',B_206,C_207) = '#skF_4'
      | ~ v1_funct_2(C_207,'#skF_4',B_206)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_206))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1340,c_1340,c_1340,c_24])).

tff(c_1417,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1336,c_1414])).

tff(c_1428,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_1417])).

tff(c_1327,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_630])).

tff(c_1475,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1327])).

tff(c_1587,plain,(
    ! [B_218,A_219] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),k1_relat_1(A_219))
      | ~ v2_funct_1(k5_relat_1(B_218,A_219))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1590,plain,(
    ! [B_218] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_218,'#skF_5'))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_1587])).

tff(c_1702,plain,(
    ! [B_239] :
      ( v2_funct_1(B_239)
      | ~ r1_tarski(k2_relat_1(B_239),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_239,'#skF_5'))
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_40,c_1590])).

tff(c_1708,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1322,c_1702])).

tff(c_1714,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_46,c_1708])).

tff(c_1715,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1714])).

tff(c_1335,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_543])).

tff(c_1677,plain,(
    ! [E_234,F_232,A_229,C_231,B_233,D_230] :
      ( k1_partfun1(A_229,B_233,C_231,D_230,E_234,F_232) = k5_relat_1(E_234,F_232)
      | ~ m1_subset_1(F_232,k1_zfmisc_1(k2_zfmisc_1(C_231,D_230)))
      | ~ v1_funct_1(F_232)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_229,B_233)))
      | ~ v1_funct_1(E_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1681,plain,(
    ! [A_229,B_233,E_234] :
      ( k1_partfun1(A_229,B_233,'#skF_4','#skF_4',E_234,'#skF_5') = k5_relat_1(E_234,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_229,B_233)))
      | ~ v1_funct_1(E_234) ) ),
    inference(resolution,[status(thm)],[c_1336,c_1677])).

tff(c_1833,plain,(
    ! [A_258,B_259,E_260] :
      ( k1_partfun1(A_258,B_259,'#skF_4','#skF_4',E_260,'#skF_5') = k5_relat_1(E_260,'#skF_5')
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_1(E_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1681])).

tff(c_1836,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1335,c_1833])).

tff(c_1850,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1836])).

tff(c_1332,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_1319,c_558])).

tff(c_1856,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_1332])).

tff(c_1858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1715,c_1856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.72  
% 3.73/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.73  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.73/1.73  
% 3.73/1.73  %Foreground sorts:
% 3.73/1.73  
% 3.73/1.73  
% 3.73/1.73  %Background operators:
% 3.73/1.73  
% 3.73/1.73  
% 3.73/1.73  %Foreground operators:
% 3.73/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.73/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.73/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.73  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.73/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.73/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.73  
% 3.73/1.75  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.73/1.75  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.73/1.75  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.73/1.75  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.73/1.75  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.73/1.75  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.73/1.75  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.73/1.75  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 3.73/1.75  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.73/1.75  tff(c_30, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_62, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.75  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_62])).
% 3.73/1.75  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_76, plain, (![A_35, B_36, C_37]: (k2_relset_1(A_35, B_36, C_37)=k2_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.73/1.75  tff(c_88, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_76])).
% 3.73/1.75  tff(c_159, plain, (![A_52, B_53, C_54]: (m1_subset_1(k2_relset_1(A_52, B_53, C_54), k1_zfmisc_1(B_53)) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.75  tff(c_177, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_159])).
% 3.73/1.75  tff(c_186, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_177])).
% 3.73/1.75  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.75  tff(c_192, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_186, c_2])).
% 3.73/1.75  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_62])).
% 3.73/1.75  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_32, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_47, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 3.73/1.75  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_120, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.75  tff(c_133, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_120])).
% 3.73/1.75  tff(c_308, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.75  tff(c_322, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_308])).
% 3.73/1.75  tff(c_330, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_133, c_322])).
% 3.73/1.75  tff(c_331, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_47, c_330])).
% 3.73/1.75  tff(c_411, plain, (![B_93, A_94]: (v2_funct_1(B_93) | ~r1_tarski(k2_relat_1(B_93), k1_relat_1(A_94)) | ~v2_funct_1(k5_relat_1(B_93, A_94)) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.75  tff(c_417, plain, (![B_93]: (v2_funct_1(B_93) | ~r1_tarski(k2_relat_1(B_93), '#skF_2') | ~v2_funct_1(k5_relat_1(B_93, '#skF_5')) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_411])).
% 3.73/1.75  tff(c_423, plain, (![B_96]: (v2_funct_1(B_96) | ~r1_tarski(k2_relat_1(B_96), '#skF_2') | ~v2_funct_1(k5_relat_1(B_96, '#skF_5')) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40, c_417])).
% 3.73/1.75  tff(c_426, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_423])).
% 3.73/1.75  tff(c_429, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46, c_426])).
% 3.73/1.75  tff(c_430, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_30, c_429])).
% 3.73/1.75  tff(c_431, plain, (![C_99, B_101, F_100, D_98, A_97, E_102]: (k1_partfun1(A_97, B_101, C_99, D_98, E_102, F_100)=k5_relat_1(E_102, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_98))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_97, B_101))) | ~v1_funct_1(E_102))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.75  tff(c_441, plain, (![A_97, B_101, E_102]: (k1_partfun1(A_97, B_101, '#skF_2', '#skF_3', E_102, '#skF_5')=k5_relat_1(E_102, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_97, B_101))) | ~v1_funct_1(E_102))), inference(resolution, [status(thm)], [c_36, c_431])).
% 3.73/1.75  tff(c_499, plain, (![A_109, B_110, E_111]: (k1_partfun1(A_109, B_110, '#skF_2', '#skF_3', E_111, '#skF_5')=k5_relat_1(E_111, '#skF_5') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(E_111))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_441])).
% 3.73/1.75  tff(c_510, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_499])).
% 3.73/1.75  tff(c_518, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_510])).
% 3.73/1.75  tff(c_34, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_522, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_34])).
% 3.73/1.75  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_522])).
% 3.73/1.75  tff(c_526, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.73/1.75  tff(c_525, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 3.73/1.75  tff(c_531, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_525])).
% 3.73/1.75  tff(c_543, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_42])).
% 3.73/1.75  tff(c_559, plain, (![C_116, A_117, B_118]: (v1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.75  tff(c_571, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_543, c_559])).
% 3.73/1.75  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.73/1.75  tff(c_541, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_44])).
% 3.73/1.75  tff(c_18, plain, (![C_20, A_18]: (k1_xboole_0=C_20 | ~v1_funct_2(C_20, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.75  tff(c_713, plain, (![C_142, A_143]: (C_142='#skF_3' | ~v1_funct_2(C_142, A_143, '#skF_3') | A_143='#skF_3' | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_526, c_526, c_526, c_18])).
% 3.73/1.75  tff(c_724, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_543, c_713])).
% 3.73/1.75  tff(c_732, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_724])).
% 3.73/1.75  tff(c_737, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_732])).
% 3.73/1.75  tff(c_584, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.73/1.75  tff(c_596, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_543, c_584])).
% 3.73/1.75  tff(c_657, plain, (![A_136, B_137, C_138]: (m1_subset_1(k2_relset_1(A_136, B_137, C_138), k1_zfmisc_1(B_137)) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.75  tff(c_678, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_596, c_657])).
% 3.73/1.75  tff(c_686, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_678])).
% 3.73/1.75  tff(c_694, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_686, c_2])).
% 3.73/1.75  tff(c_739, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_694])).
% 3.73/1.75  tff(c_542, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_36])).
% 3.73/1.75  tff(c_572, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_542, c_559])).
% 3.73/1.75  tff(c_540, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_38])).
% 3.73/1.75  tff(c_755, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_540])).
% 3.73/1.75  tff(c_617, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.75  tff(c_630, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_542, c_617])).
% 3.73/1.75  tff(c_744, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_630])).
% 3.73/1.75  tff(c_753, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_542])).
% 3.73/1.75  tff(c_757, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_737, c_526])).
% 3.73/1.75  tff(c_24, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.75  tff(c_897, plain, (![B_146, C_147]: (k1_relset_1('#skF_1', B_146, C_147)='#skF_1' | ~v1_funct_2(C_147, '#skF_1', B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_146))))), inference(demodulation, [status(thm), theory('equality')], [c_757, c_757, c_757, c_757, c_24])).
% 3.73/1.75  tff(c_900, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_753, c_897])).
% 3.73/1.75  tff(c_914, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_755, c_744, c_900])).
% 3.73/1.75  tff(c_1096, plain, (![B_165, A_166]: (v2_funct_1(B_165) | ~r1_tarski(k2_relat_1(B_165), k1_relat_1(A_166)) | ~v2_funct_1(k5_relat_1(B_165, A_166)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.75  tff(c_1102, plain, (![B_165]: (v2_funct_1(B_165) | ~r1_tarski(k2_relat_1(B_165), '#skF_1') | ~v2_funct_1(k5_relat_1(B_165, '#skF_5')) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_914, c_1096])).
% 3.73/1.75  tff(c_1165, plain, (![B_180]: (v2_funct_1(B_180) | ~r1_tarski(k2_relat_1(B_180), '#skF_1') | ~v2_funct_1(k5_relat_1(B_180, '#skF_5')) | ~v1_funct_1(B_180) | ~v1_relat_1(B_180))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_40, c_1102])).
% 3.73/1.75  tff(c_1171, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_739, c_1165])).
% 3.73/1.75  tff(c_1177, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_46, c_1171])).
% 3.73/1.75  tff(c_1178, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1177])).
% 3.73/1.75  tff(c_752, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_543])).
% 3.73/1.75  tff(c_1146, plain, (![C_176, A_174, B_178, F_177, D_175, E_179]: (k1_partfun1(A_174, B_178, C_176, D_175, E_179, F_177)=k5_relat_1(E_179, F_177) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(C_176, D_175))) | ~v1_funct_1(F_177) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_174, B_178))) | ~v1_funct_1(E_179))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.75  tff(c_1148, plain, (![A_174, B_178, E_179]: (k1_partfun1(A_174, B_178, '#skF_1', '#skF_1', E_179, '#skF_5')=k5_relat_1(E_179, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_174, B_178))) | ~v1_funct_1(E_179))), inference(resolution, [status(thm)], [c_753, c_1146])).
% 3.73/1.75  tff(c_1289, plain, (![A_201, B_202, E_203]: (k1_partfun1(A_201, B_202, '#skF_1', '#skF_1', E_203, '#skF_5')=k5_relat_1(E_203, '#skF_5') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_1(E_203))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1148])).
% 3.73/1.75  tff(c_1295, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_752, c_1289])).
% 3.73/1.75  tff(c_1309, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1295])).
% 3.73/1.75  tff(c_558, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_531, c_34])).
% 3.73/1.75  tff(c_749, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_737, c_558])).
% 3.73/1.75  tff(c_1316, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_749])).
% 3.73/1.75  tff(c_1318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1178, c_1316])).
% 3.73/1.75  tff(c_1319, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_732])).
% 3.73/1.75  tff(c_1322, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_694])).
% 3.73/1.75  tff(c_1338, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_540])).
% 3.73/1.75  tff(c_1336, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_542])).
% 3.73/1.75  tff(c_1340, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_526])).
% 3.73/1.75  tff(c_1414, plain, (![B_206, C_207]: (k1_relset_1('#skF_4', B_206, C_207)='#skF_4' | ~v1_funct_2(C_207, '#skF_4', B_206) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_206))))), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1340, c_1340, c_1340, c_24])).
% 3.73/1.75  tff(c_1417, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1336, c_1414])).
% 3.73/1.75  tff(c_1428, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_1417])).
% 3.73/1.75  tff(c_1327, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_630])).
% 3.73/1.75  tff(c_1475, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1327])).
% 3.73/1.75  tff(c_1587, plain, (![B_218, A_219]: (v2_funct_1(B_218) | ~r1_tarski(k2_relat_1(B_218), k1_relat_1(A_219)) | ~v2_funct_1(k5_relat_1(B_218, A_219)) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | ~v1_funct_1(A_219) | ~v1_relat_1(A_219))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.75  tff(c_1590, plain, (![B_218]: (v2_funct_1(B_218) | ~r1_tarski(k2_relat_1(B_218), '#skF_4') | ~v2_funct_1(k5_relat_1(B_218, '#skF_5')) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1475, c_1587])).
% 3.73/1.75  tff(c_1702, plain, (![B_239]: (v2_funct_1(B_239) | ~r1_tarski(k2_relat_1(B_239), '#skF_4') | ~v2_funct_1(k5_relat_1(B_239, '#skF_5')) | ~v1_funct_1(B_239) | ~v1_relat_1(B_239))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_40, c_1590])).
% 3.73/1.75  tff(c_1708, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1322, c_1702])).
% 3.73/1.75  tff(c_1714, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_46, c_1708])).
% 3.73/1.75  tff(c_1715, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1714])).
% 3.73/1.75  tff(c_1335, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_543])).
% 3.73/1.75  tff(c_1677, plain, (![E_234, F_232, A_229, C_231, B_233, D_230]: (k1_partfun1(A_229, B_233, C_231, D_230, E_234, F_232)=k5_relat_1(E_234, F_232) | ~m1_subset_1(F_232, k1_zfmisc_1(k2_zfmisc_1(C_231, D_230))) | ~v1_funct_1(F_232) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_229, B_233))) | ~v1_funct_1(E_234))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.75  tff(c_1681, plain, (![A_229, B_233, E_234]: (k1_partfun1(A_229, B_233, '#skF_4', '#skF_4', E_234, '#skF_5')=k5_relat_1(E_234, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_229, B_233))) | ~v1_funct_1(E_234))), inference(resolution, [status(thm)], [c_1336, c_1677])).
% 3.73/1.75  tff(c_1833, plain, (![A_258, B_259, E_260]: (k1_partfun1(A_258, B_259, '#skF_4', '#skF_4', E_260, '#skF_5')=k5_relat_1(E_260, '#skF_5') | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_1(E_260))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1681])).
% 3.73/1.75  tff(c_1836, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1335, c_1833])).
% 3.73/1.75  tff(c_1850, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1836])).
% 3.73/1.75  tff(c_1332, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_1319, c_558])).
% 3.73/1.75  tff(c_1856, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_1332])).
% 3.73/1.75  tff(c_1858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1715, c_1856])).
% 3.73/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.75  
% 3.73/1.75  Inference rules
% 3.73/1.75  ----------------------
% 3.73/1.75  #Ref     : 0
% 3.73/1.75  #Sup     : 366
% 3.73/1.75  #Fact    : 0
% 3.73/1.75  #Define  : 0
% 3.73/1.75  #Split   : 6
% 3.73/1.75  #Chain   : 0
% 3.73/1.75  #Close   : 0
% 3.73/1.75  
% 3.73/1.75  Ordering : KBO
% 3.73/1.75  
% 3.73/1.75  Simplification rules
% 3.73/1.75  ----------------------
% 3.73/1.75  #Subsume      : 8
% 3.73/1.75  #Demod        : 357
% 3.73/1.75  #Tautology    : 194
% 3.73/1.75  #SimpNegUnit  : 15
% 3.73/1.75  #BackRed      : 49
% 3.73/1.75  
% 3.73/1.75  #Partial instantiations: 0
% 3.73/1.75  #Strategies tried      : 1
% 3.73/1.75  
% 3.73/1.75  Timing (in seconds)
% 3.73/1.75  ----------------------
% 3.73/1.75  Preprocessing        : 0.35
% 3.73/1.75  Parsing              : 0.19
% 3.73/1.75  CNF conversion       : 0.02
% 3.73/1.75  Main loop            : 0.54
% 3.73/1.75  Inferencing          : 0.21
% 3.73/1.75  Reduction            : 0.17
% 3.73/1.75  Demodulation         : 0.12
% 3.73/1.75  BG Simplification    : 0.03
% 3.73/1.75  Subsumption          : 0.09
% 3.73/1.75  Abstraction          : 0.03
% 3.73/1.75  MUC search           : 0.00
% 3.73/1.75  Cooper               : 0.00
% 3.73/1.75  Total                : 0.94
% 3.73/1.75  Index Insertion      : 0.00
% 3.73/1.75  Index Deletion       : 0.00
% 3.73/1.75  Index Matching       : 0.00
% 3.73/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
