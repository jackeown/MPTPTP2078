%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 702 expanded)
%              Number of leaves         :   36 ( 243 expanded)
%              Depth                    :   11
%              Number of atoms          :  290 (1953 expanded)
%              Number of equality atoms :  107 ( 565 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_117,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1062,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1068,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1062])).

tff(c_1075,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1068])).

tff(c_22,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_128,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_139,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_128])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_139])).

tff(c_144,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_167,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_206,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_209,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_206])).

tff(c_215,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_209])).

tff(c_18,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_177,plain,(
    ! [A_42] :
      ( k1_relat_1(k2_funct_1(A_42)) = k2_relat_1(A_42)
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [A_22] :
      ( v1_funct_2(A_22,k1_relat_1(A_22),k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_840,plain,(
    ! [A_103] :
      ( v1_funct_2(k2_funct_1(A_103),k2_relat_1(A_103),k2_relat_1(k2_funct_1(A_103)))
      | ~ v1_funct_1(k2_funct_1(A_103))
      | ~ v1_relat_1(k2_funct_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_52])).

tff(c_843,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_840])).

tff(c_854,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_145,c_843])).

tff(c_857,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_854])).

tff(c_860,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_857])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_860])).

tff(c_866,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_125,c_12])).

tff(c_154,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_218,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_154])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_290,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_306,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_290])).

tff(c_612,plain,(
    ! [B_86,A_87,C_88] :
      ( k1_xboole_0 = B_86
      | k1_relset_1(A_87,B_86,C_88) = A_87
      | ~ v1_funct_2(C_88,A_87,B_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_624,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_612])).

tff(c_637,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_306,c_624])).

tff(c_638,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_637])).

tff(c_20,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52))))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_914,plain,(
    ! [A_105] :
      ( m1_subset_1(k2_funct_1(A_105),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_105)),k1_relat_1(A_105))))
      | ~ v1_funct_1(k2_funct_1(A_105))
      | ~ v1_relat_1(k2_funct_1(A_105))
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_239])).

tff(c_934,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_914])).

tff(c_951,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_866,c_145,c_934])).

tff(c_973,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_951])).

tff(c_987,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_215,c_973])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_987])).

tff(c_990,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1078,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_154])).

tff(c_1099,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1111,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1099])).

tff(c_1414,plain,(
    ! [B_149,A_150,C_151] :
      ( k1_xboole_0 = B_149
      | k1_relset_1(A_150,B_149,C_151) = A_150
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1429,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1414])).

tff(c_1444,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1111,c_1429])).

tff(c_1445,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1078,c_1444])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_125,c_14])).

tff(c_992,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_1455,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_992])).

tff(c_991,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1110,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_991,c_1099])).

tff(c_1533,plain,(
    ! [B_157,C_158,A_159] :
      ( k1_xboole_0 = B_157
      | v1_funct_2(C_158,A_159,B_157)
      | k1_relset_1(A_159,B_157,C_158) != A_159
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1542,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_991,c_1533])).

tff(c_1553,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1542])).

tff(c_1554,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_1455,c_1553])).

tff(c_1563,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1554])).

tff(c_1566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_1075,c_1563])).

tff(c_1567,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1577,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1567,c_8])).

tff(c_1570,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_154])).

tff(c_1622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1577,c_1570])).

tff(c_1623,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1632,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_2])).

tff(c_1624,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_1994,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1624])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1630,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1623,c_10])).

tff(c_2288,plain,(
    ! [B_242,A_243] :
      ( v1_funct_2(B_242,k1_relat_1(B_242),A_243)
      | ~ r1_tarski(k2_relat_1(B_242),A_243)
      | ~ v1_funct_1(B_242)
      | ~ v1_relat_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2294,plain,(
    ! [A_243] :
      ( v1_funct_2('#skF_3','#skF_3',A_243)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_243)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_2288])).

tff(c_2296,plain,(
    ! [A_243] : v1_funct_2('#skF_3','#skF_3',A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_1632,c_1994,c_2294])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1628,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_4])).

tff(c_2198,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2202,plain,(
    ! [A_235,B_236] : k2_relset_1(A_235,B_236,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1628,c_2198])).

tff(c_2204,plain,(
    ! [A_235,B_236] : k2_relset_1(A_235,B_236,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_2202])).

tff(c_2205,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_64])).

tff(c_108,plain,(
    ! [A_32] :
      ( v1_relat_1(k2_funct_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [A_32] :
      ( k2_relat_1(k2_funct_1(A_32)) != k1_xboole_0
      | k2_funct_1(A_32) = k1_xboole_0
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_108,c_12])).

tff(c_1761,plain,(
    ! [A_181] :
      ( k2_relat_1(k2_funct_1(A_181)) != '#skF_3'
      | k2_funct_1(A_181) = '#skF_3'
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1623,c_115])).

tff(c_1979,plain,(
    ! [A_211] :
      ( k1_relat_1(A_211) != '#skF_3'
      | k2_funct_1(A_211) = '#skF_3'
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211)
      | ~ v2_funct_1(A_211)
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1761])).

tff(c_1982,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1979])).

tff(c_1985,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_1630,c_1982])).

tff(c_1648,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1624])).

tff(c_1776,plain,(
    ! [A_185,B_186,C_187] :
      ( k2_relset_1(A_185,B_186,C_187) = k2_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1783,plain,(
    ! [A_185,B_186] : k2_relset_1(A_185,B_186,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1628,c_1776])).

tff(c_1786,plain,(
    ! [A_185,B_186] : k2_relset_1(A_185,B_186,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1783])).

tff(c_1794,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_64])).

tff(c_1642,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_1802,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1794,c_1642])).

tff(c_1986,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_1802])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1986])).

tff(c_1992,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_32,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2019,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1992,c_32])).

tff(c_2056,plain,(
    ! [A_223] :
      ( k1_relat_1(A_223) != '#skF_3'
      | A_223 = '#skF_3'
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1623,c_14])).

tff(c_2066,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2019,c_2056])).

tff(c_2085,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2066])).

tff(c_2088,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2085])).

tff(c_2091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_1994,c_2088])).

tff(c_2092,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2066])).

tff(c_2040,plain,(
    ! [A_222] :
      ( k2_relat_1(A_222) != '#skF_3'
      | A_222 = '#skF_3'
      | ~ v1_relat_1(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1623,c_12])).

tff(c_2050,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2019,c_2040])).

tff(c_2072,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2050])).

tff(c_2094,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_2072])).

tff(c_2101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_2094])).

tff(c_2102,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2050])).

tff(c_1991,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_2108,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_1991])).

tff(c_2213,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2205,c_2108])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2296,c_2213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.71  
% 3.95/1.71  %Foreground sorts:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Background operators:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Foreground operators:
% 3.95/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.95/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.71  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.95/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.71  
% 4.28/1.73  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.28/1.73  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.28/1.73  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.28/1.73  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.28/1.73  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.28/1.73  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.28/1.73  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.28/1.73  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.28/1.73  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.28/1.73  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.28/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.28/1.73  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.28/1.73  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.28/1.73  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_117, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.28/1.73  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_117])).
% 4.28/1.73  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_1062, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.28/1.73  tff(c_1068, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1062])).
% 4.28/1.73  tff(c_1075, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1068])).
% 4.28/1.73  tff(c_22, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.73  tff(c_16, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.73  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_128, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.28/1.73  tff(c_139, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_128])).
% 4.28/1.73  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_139])).
% 4.28/1.73  tff(c_144, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 4.28/1.73  tff(c_167, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_206, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.28/1.73  tff(c_209, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_206])).
% 4.28/1.73  tff(c_215, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_209])).
% 4.28/1.73  tff(c_18, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.73  tff(c_145, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 4.28/1.73  tff(c_177, plain, (![A_42]: (k1_relat_1(k2_funct_1(A_42))=k2_relat_1(A_42) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.73  tff(c_52, plain, (![A_22]: (v1_funct_2(A_22, k1_relat_1(A_22), k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.28/1.73  tff(c_840, plain, (![A_103]: (v1_funct_2(k2_funct_1(A_103), k2_relat_1(A_103), k2_relat_1(k2_funct_1(A_103))) | ~v1_funct_1(k2_funct_1(A_103)) | ~v1_relat_1(k2_funct_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_177, c_52])).
% 4.28/1.73  tff(c_843, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215, c_840])).
% 4.28/1.73  tff(c_854, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_145, c_843])).
% 4.28/1.73  tff(c_857, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_854])).
% 4.28/1.73  tff(c_860, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_857])).
% 4.28/1.73  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_860])).
% 4.28/1.73  tff(c_866, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_854])).
% 4.28/1.73  tff(c_12, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.28/1.73  tff(c_152, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_125, c_12])).
% 4.28/1.73  tff(c_154, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_152])).
% 4.28/1.73  tff(c_218, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_154])).
% 4.28/1.73  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.28/1.73  tff(c_290, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.73  tff(c_306, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_290])).
% 4.28/1.73  tff(c_612, plain, (![B_86, A_87, C_88]: (k1_xboole_0=B_86 | k1_relset_1(A_87, B_86, C_88)=A_87 | ~v1_funct_2(C_88, A_87, B_86) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.28/1.73  tff(c_624, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_612])).
% 4.28/1.73  tff(c_637, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_306, c_624])).
% 4.28/1.73  tff(c_638, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_218, c_637])).
% 4.28/1.73  tff(c_20, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.73  tff(c_239, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52)))) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.28/1.73  tff(c_914, plain, (![A_105]: (m1_subset_1(k2_funct_1(A_105), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_105)), k1_relat_1(A_105)))) | ~v1_funct_1(k2_funct_1(A_105)) | ~v1_relat_1(k2_funct_1(A_105)) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_20, c_239])).
% 4.28/1.73  tff(c_934, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_638, c_914])).
% 4.28/1.73  tff(c_951, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_866, c_145, c_934])).
% 4.28/1.73  tff(c_973, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_951])).
% 4.28/1.73  tff(c_987, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_215, c_973])).
% 4.28/1.73  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_987])).
% 4.28/1.73  tff(c_990, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_1078, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_154])).
% 4.28/1.73  tff(c_1099, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.73  tff(c_1111, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1099])).
% 4.28/1.73  tff(c_1414, plain, (![B_149, A_150, C_151]: (k1_xboole_0=B_149 | k1_relset_1(A_150, B_149, C_151)=A_150 | ~v1_funct_2(C_151, A_150, B_149) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.28/1.73  tff(c_1429, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1414])).
% 4.28/1.73  tff(c_1444, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1111, c_1429])).
% 4.28/1.73  tff(c_1445, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1078, c_1444])).
% 4.28/1.73  tff(c_14, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.28/1.73  tff(c_153, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_125, c_14])).
% 4.28/1.73  tff(c_992, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_153])).
% 4.28/1.73  tff(c_1455, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_992])).
% 4.28/1.73  tff(c_991, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_1110, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_991, c_1099])).
% 4.28/1.73  tff(c_1533, plain, (![B_157, C_158, A_159]: (k1_xboole_0=B_157 | v1_funct_2(C_158, A_159, B_157) | k1_relset_1(A_159, B_157, C_158)!=A_159 | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_157))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.28/1.73  tff(c_1542, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_991, c_1533])).
% 4.28/1.73  tff(c_1553, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1542])).
% 4.28/1.73  tff(c_1554, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_990, c_1455, c_1553])).
% 4.28/1.73  tff(c_1563, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1554])).
% 4.28/1.73  tff(c_1566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_1075, c_1563])).
% 4.28/1.73  tff(c_1567, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_153])).
% 4.28/1.73  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.73  tff(c_1577, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1567, c_8])).
% 4.28/1.73  tff(c_1570, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_154])).
% 4.28/1.73  tff(c_1622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1577, c_1570])).
% 4.28/1.73  tff(c_1623, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_152])).
% 4.28/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.73  tff(c_1632, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_2])).
% 4.28/1.73  tff(c_1624, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_152])).
% 4.28/1.73  tff(c_1994, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1624])).
% 4.28/1.73  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.73  tff(c_1630, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1623, c_10])).
% 4.28/1.73  tff(c_2288, plain, (![B_242, A_243]: (v1_funct_2(B_242, k1_relat_1(B_242), A_243) | ~r1_tarski(k2_relat_1(B_242), A_243) | ~v1_funct_1(B_242) | ~v1_relat_1(B_242))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.28/1.73  tff(c_2294, plain, (![A_243]: (v1_funct_2('#skF_3', '#skF_3', A_243) | ~r1_tarski(k2_relat_1('#skF_3'), A_243) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_2288])).
% 4.28/1.73  tff(c_2296, plain, (![A_243]: (v1_funct_2('#skF_3', '#skF_3', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_1632, c_1994, c_2294])).
% 4.28/1.73  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.28/1.73  tff(c_1628, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_4])).
% 4.28/1.73  tff(c_2198, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.28/1.73  tff(c_2202, plain, (![A_235, B_236]: (k2_relset_1(A_235, B_236, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1628, c_2198])).
% 4.28/1.73  tff(c_2204, plain, (![A_235, B_236]: (k2_relset_1(A_235, B_236, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_2202])).
% 4.28/1.73  tff(c_2205, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_64])).
% 4.28/1.73  tff(c_108, plain, (![A_32]: (v1_relat_1(k2_funct_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.73  tff(c_115, plain, (![A_32]: (k2_relat_1(k2_funct_1(A_32))!=k1_xboole_0 | k2_funct_1(A_32)=k1_xboole_0 | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_108, c_12])).
% 4.28/1.73  tff(c_1761, plain, (![A_181]: (k2_relat_1(k2_funct_1(A_181))!='#skF_3' | k2_funct_1(A_181)='#skF_3' | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1623, c_115])).
% 4.28/1.73  tff(c_1979, plain, (![A_211]: (k1_relat_1(A_211)!='#skF_3' | k2_funct_1(A_211)='#skF_3' | ~v1_funct_1(A_211) | ~v1_relat_1(A_211) | ~v2_funct_1(A_211) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1761])).
% 4.28/1.73  tff(c_1982, plain, (k1_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1979])).
% 4.28/1.73  tff(c_1985, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_1630, c_1982])).
% 4.28/1.73  tff(c_1648, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1624])).
% 4.28/1.73  tff(c_1776, plain, (![A_185, B_186, C_187]: (k2_relset_1(A_185, B_186, C_187)=k2_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.28/1.73  tff(c_1783, plain, (![A_185, B_186]: (k2_relset_1(A_185, B_186, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1628, c_1776])).
% 4.28/1.73  tff(c_1786, plain, (![A_185, B_186]: (k2_relset_1(A_185, B_186, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1648, c_1783])).
% 4.28/1.73  tff(c_1794, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_64])).
% 4.28/1.73  tff(c_1642, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_1802, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1794, c_1642])).
% 4.28/1.73  tff(c_1986, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_1802])).
% 4.28/1.73  tff(c_1990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1986])).
% 4.28/1.73  tff(c_1992, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_32, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.28/1.73  tff(c_2019, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1992, c_32])).
% 4.28/1.73  tff(c_2056, plain, (![A_223]: (k1_relat_1(A_223)!='#skF_3' | A_223='#skF_3' | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1623, c_14])).
% 4.28/1.73  tff(c_2066, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2019, c_2056])).
% 4.28/1.73  tff(c_2085, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2066])).
% 4.28/1.73  tff(c_2088, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2085])).
% 4.28/1.73  tff(c_2091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_1994, c_2088])).
% 4.28/1.73  tff(c_2092, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2066])).
% 4.28/1.73  tff(c_2040, plain, (![A_222]: (k2_relat_1(A_222)!='#skF_3' | A_222='#skF_3' | ~v1_relat_1(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1623, c_12])).
% 4.28/1.73  tff(c_2050, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2019, c_2040])).
% 4.28/1.73  tff(c_2072, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2050])).
% 4.28/1.73  tff(c_2094, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_2072])).
% 4.28/1.73  tff(c_2101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1994, c_2094])).
% 4.28/1.73  tff(c_2102, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2050])).
% 4.28/1.73  tff(c_1991, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_144])).
% 4.28/1.73  tff(c_2108, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_1991])).
% 4.28/1.73  tff(c_2213, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2205, c_2108])).
% 4.28/1.73  tff(c_2300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2296, c_2213])).
% 4.28/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.73  
% 4.28/1.73  Inference rules
% 4.28/1.73  ----------------------
% 4.28/1.73  #Ref     : 0
% 4.28/1.73  #Sup     : 465
% 4.28/1.73  #Fact    : 0
% 4.28/1.73  #Define  : 0
% 4.28/1.73  #Split   : 14
% 4.28/1.73  #Chain   : 0
% 4.28/1.73  #Close   : 0
% 4.28/1.73  
% 4.28/1.73  Ordering : KBO
% 4.28/1.73  
% 4.28/1.73  Simplification rules
% 4.28/1.73  ----------------------
% 4.28/1.73  #Subsume      : 43
% 4.28/1.73  #Demod        : 708
% 4.28/1.73  #Tautology    : 267
% 4.28/1.73  #SimpNegUnit  : 14
% 4.28/1.73  #BackRed      : 62
% 4.28/1.73  
% 4.28/1.73  #Partial instantiations: 0
% 4.28/1.73  #Strategies tried      : 1
% 4.28/1.73  
% 4.28/1.73  Timing (in seconds)
% 4.28/1.73  ----------------------
% 4.28/1.74  Preprocessing        : 0.33
% 4.28/1.74  Parsing              : 0.18
% 4.28/1.74  CNF conversion       : 0.02
% 4.28/1.74  Main loop            : 0.59
% 4.28/1.74  Inferencing          : 0.22
% 4.28/1.74  Reduction            : 0.20
% 4.28/1.74  Demodulation         : 0.15
% 4.28/1.74  BG Simplification    : 0.03
% 4.28/1.74  Subsumption          : 0.10
% 4.28/1.74  Abstraction          : 0.03
% 4.28/1.74  MUC search           : 0.00
% 4.28/1.74  Cooper               : 0.00
% 4.28/1.74  Total                : 1.01
% 4.28/1.74  Index Insertion      : 0.00
% 4.28/1.74  Index Deletion       : 0.00
% 4.28/1.74  Index Matching       : 0.00
% 4.28/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
