%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 22.59s
% Output     : CNFRefutation 22.59s
% Verified   : 
% Statistics : Number of formulae       :  215 (1882 expanded)
%              Number of leaves         :   40 ( 625 expanded)
%              Depth                    :   15
%              Number of atoms          :  388 (5071 expanded)
%              Number of equality atoms :  103 (1010 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_133,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_141,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_133])).

tff(c_76,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_70,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44540,plain,(
    ! [A_859,B_860,C_861] :
      ( k2_relset_1(A_859,B_860,C_861) = k2_relat_1(C_861)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(k2_zfmisc_1(A_859,B_860))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44549,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_44540])).

tff(c_44559,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44549])).

tff(c_40,plain,(
    ! [A_32] :
      ( k1_relat_1(k2_funct_1(A_32)) = k2_relat_1(A_32)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_31] :
      ( v1_funct_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_146])).

tff(c_151,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_34682,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_74,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34635,plain,(
    ! [A_701,B_702,C_703] :
      ( k1_relset_1(A_701,B_702,C_703) = k1_relat_1(C_703)
      | ~ m1_subset_1(C_703,k1_zfmisc_1(k2_zfmisc_1(A_701,B_702))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34645,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_34635])).

tff(c_36309,plain,(
    ! [B_777,A_778,C_779] :
      ( k1_xboole_0 = B_777
      | k1_relset_1(A_778,B_777,C_779) = A_778
      | ~ v1_funct_2(C_779,A_778,B_777)
      | ~ m1_subset_1(C_779,k1_zfmisc_1(k2_zfmisc_1(A_778,B_777))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36318,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_36309])).

tff(c_36331,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34645,c_36318])).

tff(c_36333,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_36331])).

tff(c_38,plain,(
    ! [A_32] :
      ( k2_relat_1(k2_funct_1(A_32)) = k1_relat_1(A_32)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_31] :
      ( v1_relat_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_152,plain,(
    v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_34696,plain,(
    ! [A_712,B_713,C_714] :
      ( k2_relset_1(A_712,B_713,C_714) = k2_relat_1(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(A_712,B_713))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34699,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_34696])).

tff(c_34707,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34699])).

tff(c_34609,plain,(
    ! [A_699] :
      ( k1_relat_1(k2_funct_1(A_699)) = k2_relat_1(A_699)
      | ~ v2_funct_1(A_699)
      | ~ v1_funct_1(A_699)
      | ~ v1_relat_1(A_699) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_62,plain,(
    ! [A_45] :
      ( v1_funct_2(A_45,k1_relat_1(A_45),k2_relat_1(A_45))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_39498,plain,(
    ! [A_821] :
      ( v1_funct_2(k2_funct_1(A_821),k2_relat_1(A_821),k2_relat_1(k2_funct_1(A_821)))
      | ~ v1_funct_1(k2_funct_1(A_821))
      | ~ v1_relat_1(k2_funct_1(A_821))
      | ~ v2_funct_1(A_821)
      | ~ v1_funct_1(A_821)
      | ~ v1_relat_1(A_821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34609,c_62])).

tff(c_39528,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_7',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_34707,c_39498])).

tff(c_39539,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_7',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_152,c_39528])).

tff(c_39542,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_39539])).

tff(c_39545,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_39542])).

tff(c_39549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_39545])).

tff(c_39551,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_39539])).

tff(c_34749,plain,(
    ! [A_721] :
      ( m1_subset_1(A_721,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_721),k2_relat_1(A_721))))
      | ~ v1_funct_1(A_721)
      | ~ v1_relat_1(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44016,plain,(
    ! [A_846] :
      ( m1_subset_1(k2_funct_1(A_846),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_846),k2_relat_1(k2_funct_1(A_846)))))
      | ~ v1_funct_1(k2_funct_1(A_846))
      | ~ v1_relat_1(k2_funct_1(A_846))
      | ~ v2_funct_1(A_846)
      | ~ v1_funct_1(A_846)
      | ~ v1_relat_1(A_846) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_34749])).

tff(c_44079,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1(k2_funct_1('#skF_8')))))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_34707,c_44016])).

tff(c_44102,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1(k2_funct_1('#skF_8'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_39551,c_152,c_44079])).

tff(c_44125,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_relat_1('#skF_8'))))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_44102])).

tff(c_44137,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_36333,c_44125])).

tff(c_44139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34682,c_44137])).

tff(c_44140,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_36331])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44174,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44140,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44171,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44140,c_44140,c_12])).

tff(c_34764,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_34707,c_34749])).

tff(c_34782,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_34764])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34815,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_34782,c_16])).

tff(c_34826,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_34815])).

tff(c_44338,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44171,c_34826])).

tff(c_44344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44174,c_44338])).

tff(c_44345,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_34815])).

tff(c_121,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_124,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_44352,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_44345,c_124])).

tff(c_44373,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44352,c_44352,c_12])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44374,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44352,c_44352,c_30])).

tff(c_44384,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44374,c_34707])).

tff(c_153,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_72,c_153])).

tff(c_158,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_44405,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44384,c_158])).

tff(c_44478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44345,c_44373,c_44405])).

tff(c_44479,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_44480,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_44,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44490,plain,(
    k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_44480,c_44])).

tff(c_46188,plain,(
    ! [B_923,C_924,A_925] :
      ( k1_xboole_0 = B_923
      | v1_funct_2(C_924,A_925,B_923)
      | k1_relset_1(A_925,B_923,C_924) != A_925
      | ~ m1_subset_1(C_924,k1_zfmisc_1(k2_zfmisc_1(A_925,B_923))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46194,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_44480,c_46188])).

tff(c_46206,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44490,c_46194])).

tff(c_46207,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_44479,c_46206])).

tff(c_46212,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_46207])).

tff(c_46215,plain,
    ( k2_relat_1('#skF_8') != '#skF_7'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_46212])).

tff(c_46218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_44559,c_46215])).

tff(c_46219,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46207])).

tff(c_46253,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46219,c_6])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46249,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_6',B_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46219,c_46219,c_14])).

tff(c_46424,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46249,c_158])).

tff(c_46428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46253,c_46424])).

tff(c_46429,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_46436,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46429,c_124])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46443,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_32])).

tff(c_46430,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127434,plain,(
    ! [A_11015] :
      ( A_11015 = '#skF_8'
      | ~ v1_xboole_0(A_11015) ) ),
    inference(resolution,[status(thm)],[c_46429,c_8])).

tff(c_127441,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46430,c_127434])).

tff(c_127481,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127441,c_72])).

tff(c_46440,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_8',B_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_14])).

tff(c_127707,plain,(
    ! [A_11033,B_11034,C_11035] :
      ( k1_relset_1(A_11033,B_11034,C_11035) = k1_relat_1(C_11035)
      | ~ m1_subset_1(C_11035,k1_zfmisc_1(k2_zfmisc_1(A_11033,B_11034))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_127714,plain,(
    ! [B_11036,C_11037] :
      ( k1_relset_1('#skF_8',B_11036,C_11037) = k1_relat_1(C_11037)
      | ~ m1_subset_1(C_11037,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46440,c_127707])).

tff(c_127716,plain,(
    ! [B_11036] : k1_relset_1('#skF_8',B_11036,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_127481,c_127714])).

tff(c_127718,plain,(
    ! [B_11036] : k1_relset_1('#skF_8',B_11036,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46443,c_127716])).

tff(c_52,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_127923,plain,(
    ! [C_11061,B_11062] :
      ( v1_funct_2(C_11061,'#skF_8',B_11062)
      | k1_relset_1('#skF_8',B_11062,C_11061) != '#skF_8'
      | ~ m1_subset_1(C_11061,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_46436,c_46436,c_78])).

tff(c_127925,plain,(
    ! [B_11062] :
      ( v1_funct_2('#skF_8','#skF_8',B_11062)
      | k1_relset_1('#skF_8',B_11062,'#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_127481,c_127923])).

tff(c_127928,plain,(
    ! [B_11062] : v1_funct_2('#skF_8','#skF_8',B_11062) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127718,c_127925])).

tff(c_46442,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_30])).

tff(c_127557,plain,(
    ! [A_11022] :
      ( v1_funct_2(A_11022,k1_relat_1(A_11022),k2_relat_1(A_11022))
      | ~ v1_funct_1(A_11022)
      | ~ v1_relat_1(A_11022) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_127560,plain,
    ( v1_funct_2('#skF_8','#skF_8',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46443,c_127557])).

tff(c_127565,plain,(
    v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_46442,c_127560])).

tff(c_48,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_42,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_79,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_127588,plain,(
    ! [A_11024] :
      ( v1_funct_2('#skF_8',A_11024,'#skF_8')
      | A_11024 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127481,c_46436,c_46436,c_46436,c_46436,c_46436,c_79])).

tff(c_46441,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_12])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46450,plain,(
    ! [B_8,A_7] :
      ( B_8 = '#skF_8'
      | A_7 = '#skF_8'
      | k2_zfmisc_1(A_7,B_8) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46436,c_46436,c_46436,c_10])).

tff(c_127491,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_127441,c_46450])).

tff(c_127499,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_127491])).

tff(c_46464,plain,(
    ! [A_932] :
      ( A_932 = '#skF_8'
      | ~ v1_xboole_0(A_932) ) ),
    inference(resolution,[status(thm)],[c_46429,c_8])).

tff(c_46471,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46430,c_46464])).

tff(c_46521,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_46471,c_46450])).

tff(c_46529,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_46521])).

tff(c_46463,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_46530,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46529,c_46463])).

tff(c_46534,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46441,c_46530])).

tff(c_46579,plain,(
    ! [A_942] :
      ( k2_relat_1(k2_funct_1(A_942)) = k1_relat_1(A_942)
      | ~ v2_funct_1(A_942)
      | ~ v1_funct_1(A_942)
      | ~ v1_relat_1(A_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_78142,plain,(
    ! [A_4096] :
      ( v1_funct_2(k2_funct_1(A_4096),k1_relat_1(k2_funct_1(A_4096)),k1_relat_1(A_4096))
      | ~ v1_funct_1(k2_funct_1(A_4096))
      | ~ v1_relat_1(k2_funct_1(A_4096))
      | ~ v2_funct_1(A_4096)
      | ~ v1_funct_1(A_4096)
      | ~ v1_relat_1(A_4096) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46579,c_62])).

tff(c_78163,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46443,c_78142])).

tff(c_78165,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_152,c_78163])).

tff(c_78166,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_78165])).

tff(c_78169,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_78166])).

tff(c_78173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_78169])).

tff(c_78175,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_78165])).

tff(c_46675,plain,(
    ! [A_962] :
      ( m1_subset_1(A_962,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_962),k2_relat_1(A_962))))
      | ~ v1_funct_1(A_962)
      | ~ v1_relat_1(A_962) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_98420,plain,(
    ! [A_7685] :
      ( m1_subset_1(k2_funct_1(A_7685),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_7685)),k1_relat_1(A_7685))))
      | ~ v1_funct_1(k2_funct_1(A_7685))
      | ~ v1_relat_1(k2_funct_1(A_7685))
      | ~ v2_funct_1(A_7685)
      | ~ v1_funct_1(A_7685)
      | ~ v1_relat_1(A_7685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_46675])).

tff(c_98483,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46443,c_98420])).

tff(c_98491,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_78175,c_152,c_46441,c_98483])).

tff(c_98493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46534,c_98491])).

tff(c_98494,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_46521])).

tff(c_98496,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98494,c_46463])).

tff(c_98500,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46440,c_98496])).

tff(c_98545,plain,(
    ! [A_7741] :
      ( k1_relat_1(k2_funct_1(A_7741)) = k2_relat_1(A_7741)
      | ~ v2_funct_1(A_7741)
      | ~ v1_funct_1(A_7741)
      | ~ v1_relat_1(A_7741) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124982,plain,(
    ! [A_10743] :
      ( v1_funct_2(k2_funct_1(A_10743),k2_relat_1(A_10743),k2_relat_1(k2_funct_1(A_10743)))
      | ~ v1_funct_1(k2_funct_1(A_10743))
      | ~ v1_relat_1(k2_funct_1(A_10743))
      | ~ v2_funct_1(A_10743)
      | ~ v1_funct_1(A_10743)
      | ~ v1_relat_1(A_10743) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98545,c_62])).

tff(c_125165,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46442,c_124982])).

tff(c_125173,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_152,c_125165])).

tff(c_125174,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_125173])).

tff(c_125177,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_125174])).

tff(c_125181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_125177])).

tff(c_125183,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_125173])).

tff(c_98569,plain,(
    ! [A_7747] :
      ( m1_subset_1(A_7747,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_7747),k2_relat_1(A_7747))))
      | ~ v1_funct_1(A_7747)
      | ~ v1_relat_1(A_7747) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_127376,plain,(
    ! [A_10990] :
      ( m1_subset_1(k2_funct_1(A_10990),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_10990)),k1_relat_1(A_10990))))
      | ~ v1_funct_1(k2_funct_1(A_10990))
      | ~ v1_relat_1(k2_funct_1(A_10990))
      | ~ v2_funct_1(A_10990)
      | ~ v1_funct_1(A_10990)
      | ~ v1_relat_1(A_10990) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_98569])).

tff(c_127421,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46443,c_127376])).

tff(c_127429,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_70,c_125183,c_152,c_46441,c_127421])).

tff(c_127431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98500,c_127429])).

tff(c_127433,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_127509,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46441,c_127499,c_127433])).

tff(c_127512,plain,
    ( v1_xboole_0(k2_funct_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_127509,c_16])).

tff(c_127515,plain,(
    v1_xboole_0(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46429,c_127512])).

tff(c_46437,plain,(
    ! [A_5] :
      ( A_5 = '#skF_8'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_46429,c_8])).

tff(c_127521,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_127515,c_46437])).

tff(c_127432,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_127501,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127499,c_127432])).

tff(c_127547,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127521,c_127501])).

tff(c_127592,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_127588,c_127547])).

tff(c_127593,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127592,c_127547])).

tff(c_127598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127565,c_127593])).

tff(c_127599,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_127491])).

tff(c_127610,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46440,c_127599,c_127433])).

tff(c_127613,plain,
    ( v1_xboole_0(k2_funct_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_127610,c_16])).

tff(c_127616,plain,(
    v1_xboole_0(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46429,c_127613])).

tff(c_127622,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_127616,c_46437])).

tff(c_127602,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127599,c_127432])).

tff(c_127648,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127622,c_127602])).

tff(c_127932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127928,c_127648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 18:16:53 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.59/12.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.59/12.81  
% 22.59/12.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.59/12.81  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 22.59/12.81  
% 22.59/12.81  %Foreground sorts:
% 22.59/12.81  
% 22.59/12.81  
% 22.59/12.81  %Background operators:
% 22.59/12.81  
% 22.59/12.81  
% 22.59/12.81  %Foreground operators:
% 22.59/12.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 22.59/12.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.59/12.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 22.59/12.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 22.59/12.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.59/12.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.59/12.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.59/12.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.59/12.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.59/12.81  tff('#skF_7', type, '#skF_7': $i).
% 22.59/12.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.59/12.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.59/12.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.59/12.81  tff('#skF_6', type, '#skF_6': $i).
% 22.59/12.81  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 22.59/12.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.59/12.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.59/12.81  tff('#skF_8', type, '#skF_8': $i).
% 22.59/12.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.59/12.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.59/12.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.59/12.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.59/12.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.59/12.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.59/12.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.59/12.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.59/12.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.59/12.81  
% 22.59/12.84  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 22.59/12.84  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 22.59/12.84  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 22.59/12.84  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 22.59/12.84  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 22.59/12.84  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 22.59/12.84  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 22.59/12.84  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 22.59/12.84  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 22.59/12.84  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 22.59/12.84  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 22.59/12.84  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 22.59/12.84  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 22.59/12.84  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_133, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 22.59/12.84  tff(c_141, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_133])).
% 22.59/12.84  tff(c_76, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_70, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_68, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_44540, plain, (![A_859, B_860, C_861]: (k2_relset_1(A_859, B_860, C_861)=k2_relat_1(C_861) | ~m1_subset_1(C_861, k1_zfmisc_1(k2_zfmisc_1(A_859, B_860))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 22.59/12.84  tff(c_44549, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_44540])).
% 22.59/12.84  tff(c_44559, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44549])).
% 22.59/12.84  tff(c_40, plain, (![A_32]: (k1_relat_1(k2_funct_1(A_32))=k2_relat_1(A_32) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.59/12.84  tff(c_34, plain, (![A_31]: (v1_funct_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.59/12.84  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_143, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_66])).
% 22.59/12.84  tff(c_146, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_143])).
% 22.59/12.84  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_146])).
% 22.59/12.84  tff(c_151, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_66])).
% 22.59/12.84  tff(c_34682, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_74, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 22.59/12.84  tff(c_34635, plain, (![A_701, B_702, C_703]: (k1_relset_1(A_701, B_702, C_703)=k1_relat_1(C_703) | ~m1_subset_1(C_703, k1_zfmisc_1(k2_zfmisc_1(A_701, B_702))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.59/12.84  tff(c_34645, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_34635])).
% 22.59/12.84  tff(c_36309, plain, (![B_777, A_778, C_779]: (k1_xboole_0=B_777 | k1_relset_1(A_778, B_777, C_779)=A_778 | ~v1_funct_2(C_779, A_778, B_777) | ~m1_subset_1(C_779, k1_zfmisc_1(k2_zfmisc_1(A_778, B_777))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.59/12.84  tff(c_36318, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_36309])).
% 22.59/12.84  tff(c_36331, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34645, c_36318])).
% 22.59/12.84  tff(c_36333, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_36331])).
% 22.59/12.84  tff(c_38, plain, (![A_32]: (k2_relat_1(k2_funct_1(A_32))=k1_relat_1(A_32) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.59/12.84  tff(c_36, plain, (![A_31]: (v1_relat_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.59/12.84  tff(c_152, plain, (v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 22.59/12.84  tff(c_34696, plain, (![A_712, B_713, C_714]: (k2_relset_1(A_712, B_713, C_714)=k2_relat_1(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(A_712, B_713))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 22.59/12.84  tff(c_34699, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_34696])).
% 22.59/12.84  tff(c_34707, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34699])).
% 22.59/12.84  tff(c_34609, plain, (![A_699]: (k1_relat_1(k2_funct_1(A_699))=k2_relat_1(A_699) | ~v2_funct_1(A_699) | ~v1_funct_1(A_699) | ~v1_relat_1(A_699))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.59/12.84  tff(c_62, plain, (![A_45]: (v1_funct_2(A_45, k1_relat_1(A_45), k2_relat_1(A_45)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 22.59/12.84  tff(c_39498, plain, (![A_821]: (v1_funct_2(k2_funct_1(A_821), k2_relat_1(A_821), k2_relat_1(k2_funct_1(A_821))) | ~v1_funct_1(k2_funct_1(A_821)) | ~v1_relat_1(k2_funct_1(A_821)) | ~v2_funct_1(A_821) | ~v1_funct_1(A_821) | ~v1_relat_1(A_821))), inference(superposition, [status(thm), theory('equality')], [c_34609, c_62])).
% 22.59/12.84  tff(c_39528, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_34707, c_39498])).
% 22.59/12.84  tff(c_39539, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_152, c_39528])).
% 22.59/12.84  tff(c_39542, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_39539])).
% 22.59/12.84  tff(c_39545, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_39542])).
% 22.59/12.84  tff(c_39549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_39545])).
% 22.59/12.84  tff(c_39551, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_39539])).
% 22.59/12.84  tff(c_34749, plain, (![A_721]: (m1_subset_1(A_721, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_721), k2_relat_1(A_721)))) | ~v1_funct_1(A_721) | ~v1_relat_1(A_721))), inference(cnfTransformation, [status(thm)], [f_122])).
% 22.59/12.84  tff(c_44016, plain, (![A_846]: (m1_subset_1(k2_funct_1(A_846), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_846), k2_relat_1(k2_funct_1(A_846))))) | ~v1_funct_1(k2_funct_1(A_846)) | ~v1_relat_1(k2_funct_1(A_846)) | ~v2_funct_1(A_846) | ~v1_funct_1(A_846) | ~v1_relat_1(A_846))), inference(superposition, [status(thm), theory('equality')], [c_40, c_34749])).
% 22.59/12.84  tff(c_44079, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1(k2_funct_1('#skF_8'))))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_34707, c_44016])).
% 22.59/12.84  tff(c_44102, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1(k2_funct_1('#skF_8')))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_39551, c_152, c_44079])).
% 22.59/12.84  tff(c_44125, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_relat_1('#skF_8')))) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_38, c_44102])).
% 22.59/12.84  tff(c_44137, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_36333, c_44125])).
% 22.59/12.84  tff(c_44139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34682, c_44137])).
% 22.59/12.84  tff(c_44140, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_36331])).
% 22.59/12.84  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.59/12.84  tff(c_44174, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44140, c_6])).
% 22.59/12.84  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.59/12.84  tff(c_44171, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44140, c_44140, c_12])).
% 22.59/12.84  tff(c_34764, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_34707, c_34749])).
% 22.59/12.84  tff(c_34782, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_34764])).
% 22.59/12.84  tff(c_16, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.59/12.84  tff(c_34815, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_34782, c_16])).
% 22.59/12.84  tff(c_34826, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_34815])).
% 22.59/12.84  tff(c_44338, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44171, c_34826])).
% 22.59/12.84  tff(c_44344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44174, c_44338])).
% 22.59/12.84  tff(c_44345, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_34815])).
% 22.59/12.84  tff(c_121, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.59/12.84  tff(c_124, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_6, c_121])).
% 22.59/12.84  tff(c_44352, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_44345, c_124])).
% 22.59/12.84  tff(c_44373, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44352, c_44352, c_12])).
% 22.59/12.84  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 22.59/12.84  tff(c_44374, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_44352, c_44352, c_30])).
% 22.59/12.84  tff(c_44384, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_44374, c_34707])).
% 22.59/12.84  tff(c_153, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.59/12.84  tff(c_157, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_153])).
% 22.59/12.84  tff(c_158, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_157])).
% 22.59/12.84  tff(c_44405, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44384, c_158])).
% 22.59/12.84  tff(c_44478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44345, c_44373, c_44405])).
% 22.59/12.84  tff(c_44479, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_44480, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_44, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.59/12.84  tff(c_44490, plain, (k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_44480, c_44])).
% 22.59/12.84  tff(c_46188, plain, (![B_923, C_924, A_925]: (k1_xboole_0=B_923 | v1_funct_2(C_924, A_925, B_923) | k1_relset_1(A_925, B_923, C_924)!=A_925 | ~m1_subset_1(C_924, k1_zfmisc_1(k2_zfmisc_1(A_925, B_923))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.59/12.84  tff(c_46194, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))!='#skF_7'), inference(resolution, [status(thm)], [c_44480, c_46188])).
% 22.59/12.84  tff(c_46206, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_44490, c_46194])).
% 22.59/12.84  tff(c_46207, plain, (k1_xboole_0='#skF_6' | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_44479, c_46206])).
% 22.59/12.84  tff(c_46212, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_46207])).
% 22.59/12.84  tff(c_46215, plain, (k2_relat_1('#skF_8')!='#skF_7' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_40, c_46212])).
% 22.59/12.84  tff(c_46218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_44559, c_46215])).
% 22.59/12.84  tff(c_46219, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_46207])).
% 22.59/12.84  tff(c_46253, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46219, c_6])).
% 22.59/12.84  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.59/12.84  tff(c_46249, plain, (![B_8]: (k2_zfmisc_1('#skF_6', B_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46219, c_46219, c_14])).
% 22.59/12.84  tff(c_46424, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46249, c_158])).
% 22.59/12.84  tff(c_46428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46253, c_46424])).
% 22.59/12.84  tff(c_46429, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_157])).
% 22.59/12.84  tff(c_46436, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_46429, c_124])).
% 22.59/12.84  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 22.59/12.84  tff(c_46443, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_32])).
% 22.59/12.84  tff(c_46430, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_157])).
% 22.59/12.84  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.59/12.84  tff(c_127434, plain, (![A_11015]: (A_11015='#skF_8' | ~v1_xboole_0(A_11015))), inference(resolution, [status(thm)], [c_46429, c_8])).
% 22.59/12.84  tff(c_127441, plain, (k2_zfmisc_1('#skF_6', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_46430, c_127434])).
% 22.59/12.84  tff(c_127481, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_127441, c_72])).
% 22.59/12.84  tff(c_46440, plain, (![B_8]: (k2_zfmisc_1('#skF_8', B_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_14])).
% 22.59/12.84  tff(c_127707, plain, (![A_11033, B_11034, C_11035]: (k1_relset_1(A_11033, B_11034, C_11035)=k1_relat_1(C_11035) | ~m1_subset_1(C_11035, k1_zfmisc_1(k2_zfmisc_1(A_11033, B_11034))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.59/12.84  tff(c_127714, plain, (![B_11036, C_11037]: (k1_relset_1('#skF_8', B_11036, C_11037)=k1_relat_1(C_11037) | ~m1_subset_1(C_11037, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_46440, c_127707])).
% 22.59/12.84  tff(c_127716, plain, (![B_11036]: (k1_relset_1('#skF_8', B_11036, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_127481, c_127714])).
% 22.59/12.84  tff(c_127718, plain, (![B_11036]: (k1_relset_1('#skF_8', B_11036, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46443, c_127716])).
% 22.59/12.84  tff(c_52, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.59/12.84  tff(c_78, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52])).
% 22.59/12.84  tff(c_127923, plain, (![C_11061, B_11062]: (v1_funct_2(C_11061, '#skF_8', B_11062) | k1_relset_1('#skF_8', B_11062, C_11061)!='#skF_8' | ~m1_subset_1(C_11061, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_46436, c_46436, c_78])).
% 22.59/12.84  tff(c_127925, plain, (![B_11062]: (v1_funct_2('#skF_8', '#skF_8', B_11062) | k1_relset_1('#skF_8', B_11062, '#skF_8')!='#skF_8')), inference(resolution, [status(thm)], [c_127481, c_127923])).
% 22.59/12.84  tff(c_127928, plain, (![B_11062]: (v1_funct_2('#skF_8', '#skF_8', B_11062))), inference(demodulation, [status(thm), theory('equality')], [c_127718, c_127925])).
% 22.59/12.84  tff(c_46442, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_30])).
% 22.59/12.84  tff(c_127557, plain, (![A_11022]: (v1_funct_2(A_11022, k1_relat_1(A_11022), k2_relat_1(A_11022)) | ~v1_funct_1(A_11022) | ~v1_relat_1(A_11022))), inference(cnfTransformation, [status(thm)], [f_122])).
% 22.59/12.84  tff(c_127560, plain, (v1_funct_2('#skF_8', '#skF_8', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46443, c_127557])).
% 22.59/12.84  tff(c_127565, plain, (v1_funct_2('#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_46442, c_127560])).
% 22.59/12.84  tff(c_48, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_42, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.59/12.84  tff(c_79, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 22.59/12.84  tff(c_127588, plain, (![A_11024]: (v1_funct_2('#skF_8', A_11024, '#skF_8') | A_11024='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_127481, c_46436, c_46436, c_46436, c_46436, c_46436, c_79])).
% 22.59/12.84  tff(c_46441, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_12])).
% 22.59/12.84  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.59/12.84  tff(c_46450, plain, (![B_8, A_7]: (B_8='#skF_8' | A_7='#skF_8' | k2_zfmisc_1(A_7, B_8)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46436, c_46436, c_46436, c_10])).
% 22.59/12.84  tff(c_127491, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_127441, c_46450])).
% 22.59/12.84  tff(c_127499, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_127491])).
% 22.59/12.84  tff(c_46464, plain, (![A_932]: (A_932='#skF_8' | ~v1_xboole_0(A_932))), inference(resolution, [status(thm)], [c_46429, c_8])).
% 22.59/12.84  tff(c_46471, plain, (k2_zfmisc_1('#skF_6', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_46430, c_46464])).
% 22.59/12.84  tff(c_46521, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_46471, c_46450])).
% 22.59/12.84  tff(c_46529, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_46521])).
% 22.59/12.84  tff(c_46463, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_46530, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_46529, c_46463])).
% 22.59/12.84  tff(c_46534, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46441, c_46530])).
% 22.59/12.84  tff(c_46579, plain, (![A_942]: (k2_relat_1(k2_funct_1(A_942))=k1_relat_1(A_942) | ~v2_funct_1(A_942) | ~v1_funct_1(A_942) | ~v1_relat_1(A_942))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.59/12.84  tff(c_78142, plain, (![A_4096]: (v1_funct_2(k2_funct_1(A_4096), k1_relat_1(k2_funct_1(A_4096)), k1_relat_1(A_4096)) | ~v1_funct_1(k2_funct_1(A_4096)) | ~v1_relat_1(k2_funct_1(A_4096)) | ~v2_funct_1(A_4096) | ~v1_funct_1(A_4096) | ~v1_relat_1(A_4096))), inference(superposition, [status(thm), theory('equality')], [c_46579, c_62])).
% 22.59/12.84  tff(c_78163, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_8') | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46443, c_78142])).
% 22.59/12.84  tff(c_78165, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_8') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_152, c_78163])).
% 22.59/12.84  tff(c_78166, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_78165])).
% 22.59/12.84  tff(c_78169, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_78166])).
% 22.59/12.84  tff(c_78173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_78169])).
% 22.59/12.84  tff(c_78175, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_78165])).
% 22.59/12.84  tff(c_46675, plain, (![A_962]: (m1_subset_1(A_962, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_962), k2_relat_1(A_962)))) | ~v1_funct_1(A_962) | ~v1_relat_1(A_962))), inference(cnfTransformation, [status(thm)], [f_122])).
% 22.59/12.84  tff(c_98420, plain, (![A_7685]: (m1_subset_1(k2_funct_1(A_7685), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_7685)), k1_relat_1(A_7685)))) | ~v1_funct_1(k2_funct_1(A_7685)) | ~v1_relat_1(k2_funct_1(A_7685)) | ~v2_funct_1(A_7685) | ~v1_funct_1(A_7685) | ~v1_relat_1(A_7685))), inference(superposition, [status(thm), theory('equality')], [c_38, c_46675])).
% 22.59/12.84  tff(c_98483, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46443, c_98420])).
% 22.59/12.84  tff(c_98491, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_78175, c_152, c_46441, c_98483])).
% 22.59/12.84  tff(c_98493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46534, c_98491])).
% 22.59/12.84  tff(c_98494, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_46521])).
% 22.59/12.84  tff(c_98496, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_98494, c_46463])).
% 22.59/12.84  tff(c_98500, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46440, c_98496])).
% 22.59/12.84  tff(c_98545, plain, (![A_7741]: (k1_relat_1(k2_funct_1(A_7741))=k2_relat_1(A_7741) | ~v2_funct_1(A_7741) | ~v1_funct_1(A_7741) | ~v1_relat_1(A_7741))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.59/12.84  tff(c_124982, plain, (![A_10743]: (v1_funct_2(k2_funct_1(A_10743), k2_relat_1(A_10743), k2_relat_1(k2_funct_1(A_10743))) | ~v1_funct_1(k2_funct_1(A_10743)) | ~v1_relat_1(k2_funct_1(A_10743)) | ~v2_funct_1(A_10743) | ~v1_funct_1(A_10743) | ~v1_relat_1(A_10743))), inference(superposition, [status(thm), theory('equality')], [c_98545, c_62])).
% 22.59/12.84  tff(c_125165, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46442, c_124982])).
% 22.59/12.84  tff(c_125173, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_152, c_125165])).
% 22.59/12.84  tff(c_125174, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_125173])).
% 22.59/12.84  tff(c_125177, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_125174])).
% 22.59/12.84  tff(c_125181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_125177])).
% 22.59/12.84  tff(c_125183, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_125173])).
% 22.59/12.84  tff(c_98569, plain, (![A_7747]: (m1_subset_1(A_7747, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_7747), k2_relat_1(A_7747)))) | ~v1_funct_1(A_7747) | ~v1_relat_1(A_7747))), inference(cnfTransformation, [status(thm)], [f_122])).
% 22.59/12.84  tff(c_127376, plain, (![A_10990]: (m1_subset_1(k2_funct_1(A_10990), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_10990)), k1_relat_1(A_10990)))) | ~v1_funct_1(k2_funct_1(A_10990)) | ~v1_relat_1(k2_funct_1(A_10990)) | ~v2_funct_1(A_10990) | ~v1_funct_1(A_10990) | ~v1_relat_1(A_10990))), inference(superposition, [status(thm), theory('equality')], [c_38, c_98569])).
% 22.59/12.84  tff(c_127421, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46443, c_127376])).
% 22.59/12.84  tff(c_127429, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_70, c_125183, c_152, c_46441, c_127421])).
% 22.59/12.84  tff(c_127431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98500, c_127429])).
% 22.59/12.84  tff(c_127433, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_127509, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46441, c_127499, c_127433])).
% 22.59/12.84  tff(c_127512, plain, (v1_xboole_0(k2_funct_1('#skF_8')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_127509, c_16])).
% 22.59/12.84  tff(c_127515, plain, (v1_xboole_0(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46429, c_127512])).
% 22.59/12.84  tff(c_46437, plain, (![A_5]: (A_5='#skF_8' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_46429, c_8])).
% 22.59/12.84  tff(c_127521, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_127515, c_46437])).
% 22.59/12.84  tff(c_127432, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 22.59/12.84  tff(c_127501, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_127499, c_127432])).
% 22.59/12.84  tff(c_127547, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_127521, c_127501])).
% 22.59/12.84  tff(c_127592, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_127588, c_127547])).
% 22.59/12.84  tff(c_127593, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_127592, c_127547])).
% 22.59/12.84  tff(c_127598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127565, c_127593])).
% 22.59/12.84  tff(c_127599, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_127491])).
% 22.59/12.84  tff(c_127610, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46440, c_127599, c_127433])).
% 22.59/12.84  tff(c_127613, plain, (v1_xboole_0(k2_funct_1('#skF_8')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_127610, c_16])).
% 22.59/12.84  tff(c_127616, plain, (v1_xboole_0(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46429, c_127613])).
% 22.59/12.84  tff(c_127622, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_127616, c_46437])).
% 22.59/12.84  tff(c_127602, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_127599, c_127432])).
% 22.59/12.84  tff(c_127648, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_127622, c_127602])).
% 22.59/12.84  tff(c_127932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127928, c_127648])).
% 22.59/12.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.59/12.84  
% 22.59/12.84  Inference rules
% 22.59/12.84  ----------------------
% 22.59/12.84  #Ref     : 0
% 22.59/12.84  #Sup     : 31043
% 22.59/12.84  #Fact    : 0
% 22.59/12.84  #Define  : 0
% 22.59/12.84  #Split   : 58
% 22.59/12.84  #Chain   : 0
% 22.59/12.84  #Close   : 0
% 22.59/12.84  
% 22.59/12.84  Ordering : KBO
% 22.59/12.84  
% 22.59/12.84  Simplification rules
% 22.59/12.84  ----------------------
% 22.59/12.84  #Subsume      : 13493
% 22.59/12.84  #Demod        : 25140
% 22.59/12.84  #Tautology    : 5482
% 22.59/12.84  #SimpNegUnit  : 1878
% 22.59/12.84  #BackRed      : 508
% 22.59/12.84  
% 22.59/12.84  #Partial instantiations: 6868
% 22.59/12.84  #Strategies tried      : 1
% 22.59/12.84  
% 22.59/12.84  Timing (in seconds)
% 22.59/12.84  ----------------------
% 22.59/12.84  Preprocessing        : 0.37
% 22.59/12.84  Parsing              : 0.19
% 22.59/12.84  CNF conversion       : 0.03
% 22.59/12.84  Main loop            : 11.64
% 22.59/12.84  Inferencing          : 2.16
% 22.59/12.84  Reduction            : 3.15
% 22.59/12.84  Demodulation         : 2.30
% 22.59/12.84  BG Simplification    : 0.31
% 22.59/12.84  Subsumption          : 5.55
% 22.59/12.84  Abstraction          : 0.48
% 22.59/12.84  MUC search           : 0.00
% 22.59/12.84  Cooper               : 0.00
% 22.59/12.84  Total                : 12.08
% 22.59/12.84  Index Insertion      : 0.00
% 22.59/12.84  Index Deletion       : 0.00
% 22.59/12.84  Index Matching       : 0.00
% 22.59/12.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
