%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.78s
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

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_30,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_159,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k2_relset_1(A_52,B_53,C_54),k1_zfmisc_1(B_53))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_159])).

tff(c_186,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_177])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_192,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_186,c_24])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_120,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_347,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_361,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_347])).

tff(c_369,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_133,c_361])).

tff(c_370,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_369])).

tff(c_409,plain,(
    ! [B_93,A_94] :
      ( v2_funct_1(B_93)
      | ~ r1_tarski(k2_relat_1(B_93),k1_relat_1(A_94))
      | ~ v2_funct_1(k5_relat_1(B_93,A_94))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_415,plain,(
    ! [B_93] :
      ( v2_funct_1(B_93)
      | ~ r1_tarski(k2_relat_1(B_93),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_93,'#skF_5'))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_409])).

tff(c_421,plain,(
    ! [B_96] :
      ( v2_funct_1(B_96)
      | ~ r1_tarski(k2_relat_1(B_96),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_96,'#skF_5'))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_415])).

tff(c_424,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_421])).

tff(c_427,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46,c_424])).

tff(c_428,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_427])).

tff(c_429,plain,(
    ! [C_102,A_99,D_100,F_101,E_98,B_97] :
      ( k1_partfun1(A_99,B_97,C_102,D_100,E_98,F_101) = k5_relat_1(E_98,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_102,D_100)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_439,plain,(
    ! [A_99,B_97,E_98] :
      ( k1_partfun1(A_99,B_97,'#skF_2','#skF_3',E_98,'#skF_5') = k5_relat_1(E_98,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(resolution,[status(thm)],[c_36,c_429])).

tff(c_497,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_3',E_111,'#skF_5') = k5_relat_1(E_111,'#skF_5')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_439])).

tff(c_508,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_497])).

tff(c_516,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_508])).

tff(c_34,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_520,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_34])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_520])).

tff(c_524,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_523,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_529,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_523])).

tff(c_541,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_42])).

tff(c_557,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_569,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_541,c_557])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_539,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_44])).

tff(c_6,plain,(
    ! [C_6,A_4] :
      ( k1_xboole_0 = C_6
      | ~ v1_funct_2(C_6,A_4,k1_xboole_0)
      | k1_xboole_0 = A_4
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_711,plain,(
    ! [C_142,A_143] :
      ( C_142 = '#skF_3'
      | ~ v1_funct_2(C_142,A_143,'#skF_3')
      | A_143 = '#skF_3'
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_524,c_524,c_524,c_6])).

tff(c_722,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_541,c_711])).

tff(c_730,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_722])).

tff(c_735,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_582,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_594,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_541,c_582])).

tff(c_655,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1(k2_relset_1(A_136,B_137,C_138),k1_zfmisc_1(B_137))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_676,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_655])).

tff(c_684,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_676])).

tff(c_692,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_684,c_24])).

tff(c_737,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_692])).

tff(c_540,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_36])).

tff(c_570,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_540,c_557])).

tff(c_538,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_38])).

tff(c_753,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_735,c_538])).

tff(c_615,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_628,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_540,c_615])).

tff(c_742,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_735,c_628])).

tff(c_751,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_735,c_540])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_524])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_895,plain,(
    ! [B_146,C_147] :
      ( k1_relset_1('#skF_1',B_146,C_147) = '#skF_1'
      | ~ v1_funct_2(C_147,'#skF_1',B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_146))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_755,c_755,c_755,c_12])).

tff(c_898,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_751,c_895])).

tff(c_912,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_742,c_898])).

tff(c_1094,plain,(
    ! [B_165,A_166] :
      ( v2_funct_1(B_165)
      | ~ r1_tarski(k2_relat_1(B_165),k1_relat_1(A_166))
      | ~ v2_funct_1(k5_relat_1(B_165,A_166))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1100,plain,(
    ! [B_165] :
      ( v2_funct_1(B_165)
      | ~ r1_tarski(k2_relat_1(B_165),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_165,'#skF_5'))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_1094])).

tff(c_1163,plain,(
    ! [B_180] :
      ( v2_funct_1(B_180)
      | ~ r1_tarski(k2_relat_1(B_180),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_180,'#skF_5'))
      | ~ v1_funct_1(B_180)
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_40,c_1100])).

tff(c_1169,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_737,c_1163])).

tff(c_1175,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_46,c_1169])).

tff(c_1176,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1175])).

tff(c_750,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_541])).

tff(c_1144,plain,(
    ! [D_177,F_178,A_176,B_174,E_175,C_179] :
      ( k1_partfun1(A_176,B_174,C_179,D_177,E_175,F_178) = k5_relat_1(E_175,F_178)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_179,D_177)))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1146,plain,(
    ! [A_176,B_174,E_175] :
      ( k1_partfun1(A_176,B_174,'#skF_1','#skF_1',E_175,'#skF_5') = k5_relat_1(E_175,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(resolution,[status(thm)],[c_751,c_1144])).

tff(c_1287,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_1','#skF_1',E_203,'#skF_5') = k5_relat_1(E_203,'#skF_5')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1146])).

tff(c_1293,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_750,c_1287])).

tff(c_1307,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1293])).

tff(c_556,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_529,c_34])).

tff(c_747,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_735,c_735,c_556])).

tff(c_1314,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_747])).

tff(c_1316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1176,c_1314])).

tff(c_1317,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_1320,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_692])).

tff(c_1336,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1317,c_538])).

tff(c_1334,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1317,c_540])).

tff(c_1338,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_524])).

tff(c_1412,plain,(
    ! [B_206,C_207] :
      ( k1_relset_1('#skF_4',B_206,C_207) = '#skF_4'
      | ~ v1_funct_2(C_207,'#skF_4',B_206)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_206))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_1338,c_1338,c_1338,c_12])).

tff(c_1415,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1334,c_1412])).

tff(c_1426,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1415])).

tff(c_1325,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1317,c_628])).

tff(c_1473,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_1325])).

tff(c_1585,plain,(
    ! [B_218,A_219] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),k1_relat_1(A_219))
      | ~ v2_funct_1(k5_relat_1(B_218,A_219))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1588,plain,(
    ! [B_218] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_218,'#skF_5'))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_1585])).

tff(c_1700,plain,(
    ! [B_239] :
      ( v2_funct_1(B_239)
      | ~ r1_tarski(k2_relat_1(B_239),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_239,'#skF_5'))
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_40,c_1588])).

tff(c_1706,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1320,c_1700])).

tff(c_1712,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_46,c_1706])).

tff(c_1713,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1712])).

tff(c_1333,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_541])).

tff(c_1675,plain,(
    ! [E_230,C_234,D_232,A_231,B_229,F_233] :
      ( k1_partfun1(A_231,B_229,C_234,D_232,E_230,F_233) = k5_relat_1(E_230,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_234,D_232)))
      | ~ v1_funct_1(F_233)
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_229)))
      | ~ v1_funct_1(E_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1679,plain,(
    ! [A_231,B_229,E_230] :
      ( k1_partfun1(A_231,B_229,'#skF_4','#skF_4',E_230,'#skF_5') = k5_relat_1(E_230,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_229)))
      | ~ v1_funct_1(E_230) ) ),
    inference(resolution,[status(thm)],[c_1334,c_1675])).

tff(c_1831,plain,(
    ! [A_258,B_259,E_260] :
      ( k1_partfun1(A_258,B_259,'#skF_4','#skF_4',E_260,'#skF_5') = k5_relat_1(E_260,'#skF_5')
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_1(E_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1679])).

tff(c_1834,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1333,c_1831])).

tff(c_1848,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1834])).

tff(c_1330,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1317,c_1317,c_556])).

tff(c_1854,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1330])).

tff(c_1856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1713,c_1854])).

%------------------------------------------------------------------------------
