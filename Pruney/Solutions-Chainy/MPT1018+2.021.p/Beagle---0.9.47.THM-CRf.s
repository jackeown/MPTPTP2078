%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  138 (9074 expanded)
%              Number of leaves         :   28 (2676 expanded)
%              Depth                    :   21
%              Number of atoms          :  294 (23162 expanded)
%              Number of equality atoms :  127 (11145 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_349,plain,(
    ! [D_66,C_67,B_68,A_69] :
      ( k1_funct_1(k2_funct_1(D_66),k1_funct_1(D_66,C_67)) = C_67
      | k1_xboole_0 = B_68
      | ~ r2_hidden(C_67,A_69)
      | ~ v2_funct_1(D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68)))
      | ~ v1_funct_2(D_66,A_69,B_68)
      | ~ v1_funct_1(D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_364,plain,(
    ! [D_72,B_73] :
      ( k1_funct_1(k2_funct_1(D_72),k1_funct_1(D_72,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_73
      | ~ v2_funct_1(D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_73)))
      | ~ v1_funct_2(D_72,'#skF_1',B_73)
      | ~ v1_funct_1(D_72) ) ),
    inference(resolution,[status(thm)],[c_40,c_349])).

tff(c_369,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_364])).

tff(c_376,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_369])).

tff(c_378,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_399,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_397,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_378,c_12])).

tff(c_84,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_105,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_105])).

tff(c_131,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_131])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_438])).

tff(c_445,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_444,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_38,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_450,plain,(
    ! [D_78,B_79] :
      ( k1_funct_1(k2_funct_1(D_78),k1_funct_1(D_78,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_79
      | ~ v2_funct_1(D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_79)))
      | ~ v1_funct_2(D_78,'#skF_1',B_79)
      | ~ v1_funct_1(D_78) ) ),
    inference(resolution,[status(thm)],[c_42,c_349])).

tff(c_455,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_450])).

tff(c_462,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_444,c_38,c_455])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_36,c_462])).

tff(c_465,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_689,plain,(
    ! [B_111,C_112,A_113] :
      ( k1_xboole_0 = B_111
      | v1_funct_2(C_112,A_113,B_111)
      | k1_relset_1(A_113,B_111,C_112) != A_113
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_692,plain,(
    ! [C_112] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_112,'#skF_1','#skF_1')
      | k1_relset_1('#skF_1','#skF_1',C_112) != '#skF_1'
      | ~ m1_subset_1(C_112,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_689])).

tff(c_705,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_473,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_10])).

tff(c_483,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_719,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_483])).

tff(c_722,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_705,c_12])).

tff(c_759,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_465])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_759])).

tff(c_763,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_861,plain,(
    ! [D_130,C_131,B_132,A_133] :
      ( k1_funct_1(k2_funct_1(D_130),k1_funct_1(D_130,C_131)) = C_131
      | k1_xboole_0 = B_132
      | ~ r2_hidden(C_131,A_133)
      | ~ v2_funct_1(D_130)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(D_130,A_133,B_132)
      | ~ v1_funct_1(D_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_889,plain,(
    ! [D_135,B_136] :
      ( k1_funct_1(k2_funct_1(D_135),k1_funct_1(D_135,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_136
      | ~ v2_funct_1(D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_136)))
      | ~ v1_funct_2(D_135,'#skF_1',B_136)
      | ~ v1_funct_1(D_135) ) ),
    inference(resolution,[status(thm)],[c_40,c_861])).

tff(c_1093,plain,(
    ! [A_151,B_152] :
      ( k1_funct_1(k2_funct_1(A_151),k1_funct_1(A_151,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_152
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_2(A_151,'#skF_1',B_152)
      | ~ v1_funct_1(A_151)
      | ~ r1_tarski(A_151,k2_zfmisc_1('#skF_1',B_152)) ) ),
    inference(resolution,[status(thm)],[c_18,c_889])).

tff(c_1095,plain,(
    ! [A_151] :
      ( k1_funct_1(k2_funct_1(A_151),k1_funct_1(A_151,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = '#skF_1'
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_2(A_151,'#skF_1','#skF_1')
      | ~ v1_funct_1(A_151)
      | ~ r1_tarski(A_151,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_1093])).

tff(c_1110,plain,(
    ! [A_153] :
      ( k1_funct_1(k2_funct_1(A_153),k1_funct_1(A_153,'#skF_4')) = '#skF_4'
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_2(A_153,'#skF_1','#skF_1')
      | ~ v1_funct_1(A_153)
      | ~ r1_tarski(A_153,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_1095])).

tff(c_468,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_46])).

tff(c_1033,plain,(
    ! [D_146,B_147] :
      ( k1_funct_1(k2_funct_1(D_146),k1_funct_1(D_146,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_147
      | ~ v2_funct_1(D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_147)))
      | ~ v1_funct_2(D_146,'#skF_1',B_147)
      | ~ v1_funct_1(D_146) ) ),
    inference(resolution,[status(thm)],[c_42,c_861])).

tff(c_1035,plain,(
    ! [D_146] :
      ( k1_funct_1(k2_funct_1(D_146),k1_funct_1(D_146,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = '#skF_1'
      | ~ v2_funct_1(D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_146,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_1033])).

tff(c_1075,plain,(
    ! [D_150] :
      ( k1_funct_1(k2_funct_1(D_150),k1_funct_1(D_150,'#skF_3')) = '#skF_3'
      | ~ v2_funct_1(D_150)
      | ~ m1_subset_1(D_150,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_150,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_1035])).

tff(c_1084,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1075])).

tff(c_1088,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_468,c_44,c_1084])).

tff(c_1116,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_1088])).

tff(c_1125,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50,c_48,c_44,c_1116])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1125])).

tff(c_1129,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_1128,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_1146,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1129,c_1128])).

tff(c_1147,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_1156,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_50])).

tff(c_1151,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1147,c_468])).

tff(c_1155,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_44])).

tff(c_1153,plain,(
    k1_funct_1('#skF_1','#skF_3') = k1_funct_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1147,c_38])).

tff(c_1134,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_8])).

tff(c_1149,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1134])).

tff(c_1198,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1317,plain,(
    ! [A_178,B_179,A_180] :
      ( k1_relset_1(A_178,B_179,A_180) = k1_relat_1(A_180)
      | ~ r1_tarski(A_180,k2_zfmisc_1(A_178,B_179)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1198])).

tff(c_1332,plain,(
    ! [A_178,B_179] : k1_relset_1(A_178,B_179,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1149,c_1317])).

tff(c_1154,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_48])).

tff(c_1150,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1129])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [B_12,C_13] :
      ( k1_relset_1(k1_xboole_0,B_12,C_13) = k1_xboole_0
      | ~ v1_funct_2(C_13,k1_xboole_0,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    ! [B_12,C_13] :
      ( k1_relset_1(k1_xboole_0,B_12,C_13) = k1_xboole_0
      | ~ v1_funct_2(C_13,k1_xboole_0,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_1371,plain,(
    ! [B_187,C_188] :
      ( k1_relset_1('#skF_1',B_187,C_188) = '#skF_1'
      | ~ v1_funct_2(C_188,'#skF_1',B_187)
      | ~ m1_subset_1(C_188,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_1150,c_1150,c_51])).

tff(c_1376,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1154,c_1371])).

tff(c_1383,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_1332,c_1376])).

tff(c_26,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_1361,plain,(
    ! [C_185,B_186] :
      ( v1_funct_2(C_185,'#skF_1',B_186)
      | k1_relset_1('#skF_1',B_186,C_185) != '#skF_1'
      | ~ m1_subset_1(C_185,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_1150,c_1150,c_52])).

tff(c_1363,plain,(
    ! [B_186] :
      ( v1_funct_2('#skF_1','#skF_1',B_186)
      | k1_relset_1('#skF_1',B_186,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1151,c_1361])).

tff(c_1368,plain,(
    ! [B_186] :
      ( v1_funct_2('#skF_1','#skF_1',B_186)
      | k1_relat_1('#skF_1') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1363])).

tff(c_1397,plain,(
    ! [B_186] : v1_funct_2('#skF_1','#skF_1',B_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1368])).

tff(c_1133,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1129,c_14])).

tff(c_1169,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1147,c_1133])).

tff(c_34,plain,(
    ! [D_17,C_16,B_15,A_14] :
      ( k1_funct_1(k2_funct_1(D_17),k1_funct_1(D_17,C_16)) = C_16
      | k1_xboole_0 = B_15
      | ~ r2_hidden(C_16,A_14)
      | ~ v2_funct_1(D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_17,A_14,B_15)
      | ~ v1_funct_1(D_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1507,plain,(
    ! [D_207,C_208,B_209,A_210] :
      ( k1_funct_1(k2_funct_1(D_207),k1_funct_1(D_207,C_208)) = C_208
      | B_209 = '#skF_1'
      | ~ r2_hidden(C_208,A_210)
      | ~ v2_funct_1(D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_2(D_207,A_210,B_209)
      | ~ v1_funct_1(D_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_34])).

tff(c_1511,plain,(
    ! [D_207,B_209] :
      ( k1_funct_1(k2_funct_1(D_207),k1_funct_1(D_207,'#skF_3')) = '#skF_3'
      | B_209 = '#skF_1'
      | ~ v2_funct_1(D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_209)))
      | ~ v1_funct_2(D_207,'#skF_1',B_209)
      | ~ v1_funct_1(D_207) ) ),
    inference(resolution,[status(thm)],[c_42,c_1507])).

tff(c_1580,plain,(
    ! [D_218,B_219] :
      ( k1_funct_1(k2_funct_1(D_218),k1_funct_1(D_218,'#skF_3')) = '#skF_3'
      | B_219 = '#skF_1'
      | ~ v2_funct_1(D_218)
      | ~ m1_subset_1(D_218,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_2(D_218,'#skF_1',B_219)
      | ~ v1_funct_1(D_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_1511])).

tff(c_1590,plain,(
    ! [B_186] :
      ( k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_3')) = '#skF_3'
      | B_186 = '#skF_1'
      | ~ v2_funct_1('#skF_1')
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1397,c_1580])).

tff(c_1603,plain,(
    ! [B_186] :
      ( k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_3'
      | B_186 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1151,c_1155,c_1153,c_1590])).

tff(c_1608,plain,(
    k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1603])).

tff(c_1509,plain,(
    ! [D_207,B_209] :
      ( k1_funct_1(k2_funct_1(D_207),k1_funct_1(D_207,'#skF_4')) = '#skF_4'
      | B_209 = '#skF_1'
      | ~ v2_funct_1(D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_209)))
      | ~ v1_funct_2(D_207,'#skF_1',B_209)
      | ~ v1_funct_1(D_207) ) ),
    inference(resolution,[status(thm)],[c_40,c_1507])).

tff(c_1648,plain,(
    ! [D_222,B_223] :
      ( k1_funct_1(k2_funct_1(D_222),k1_funct_1(D_222,'#skF_4')) = '#skF_4'
      | B_223 = '#skF_1'
      | ~ v2_funct_1(D_222)
      | ~ m1_subset_1(D_222,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_2(D_222,'#skF_1',B_223)
      | ~ v1_funct_1(D_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_1509])).

tff(c_1658,plain,(
    ! [B_186] :
      ( k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_4'
      | B_186 = '#skF_1'
      | ~ v2_funct_1('#skF_1')
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1397,c_1648])).

tff(c_1673,plain,(
    ! [B_186] :
      ( '#skF_3' = '#skF_4'
      | B_186 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1151,c_1155,c_1608,c_1658])).

tff(c_1681,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1673])).

tff(c_1674,plain,(
    ! [B_186] : B_186 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1673])).

tff(c_1773,plain,(
    ! [B_505] : B_505 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1681,c_1674])).

tff(c_1785,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_1608])).

tff(c_1849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1785])).

tff(c_1881,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_1850,plain,(
    ! [B_186] : B_186 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_1961,plain,(
    ! [B_1019] : B_1019 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_1850])).

tff(c_2029,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1961,c_36])).

tff(c_2030,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_2031,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_2046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_2031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.91  
% 3.82/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.91  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.82/1.91  
% 3.82/1.91  %Foreground sorts:
% 3.82/1.91  
% 3.82/1.91  
% 3.82/1.91  %Background operators:
% 3.82/1.91  
% 3.82/1.91  
% 3.82/1.91  %Foreground operators:
% 3.82/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.91  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.82/1.91  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.82/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.82/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.91  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.91  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.82/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.91  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.91  
% 3.82/1.93  tff(f_97, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 3.82/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.82/1.93  tff(f_79, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.82/1.93  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.82/1.93  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.82/1.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.82/1.93  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.82/1.93  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.82/1.93  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.93  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_48, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_349, plain, (![D_66, C_67, B_68, A_69]: (k1_funct_1(k2_funct_1(D_66), k1_funct_1(D_66, C_67))=C_67 | k1_xboole_0=B_68 | ~r2_hidden(C_67, A_69) | ~v2_funct_1(D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))) | ~v1_funct_2(D_66, A_69, B_68) | ~v1_funct_1(D_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.93  tff(c_364, plain, (![D_72, B_73]: (k1_funct_1(k2_funct_1(D_72), k1_funct_1(D_72, '#skF_4'))='#skF_4' | k1_xboole_0=B_73 | ~v2_funct_1(D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_73))) | ~v1_funct_2(D_72, '#skF_1', B_73) | ~v1_funct_1(D_72))), inference(resolution, [status(thm)], [c_40, c_349])).
% 3.82/1.93  tff(c_369, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_364])).
% 3.82/1.93  tff(c_376, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_369])).
% 3.82/1.93  tff(c_378, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_376])).
% 3.82/1.93  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.93  tff(c_399, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_8])).
% 3.82/1.93  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.93  tff(c_397, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_378, c_12])).
% 3.82/1.93  tff(c_84, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.93  tff(c_88, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.82/1.93  tff(c_105, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.93  tff(c_112, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_88, c_105])).
% 3.82/1.93  tff(c_131, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 3.82/1.93  tff(c_438, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_131])).
% 3.82/1.93  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_438])).
% 3.82/1.93  tff(c_445, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_376])).
% 3.82/1.93  tff(c_444, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_376])).
% 3.82/1.93  tff(c_38, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.82/1.93  tff(c_450, plain, (![D_78, B_79]: (k1_funct_1(k2_funct_1(D_78), k1_funct_1(D_78, '#skF_3'))='#skF_3' | k1_xboole_0=B_79 | ~v2_funct_1(D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_79))) | ~v1_funct_2(D_78, '#skF_1', B_79) | ~v1_funct_1(D_78))), inference(resolution, [status(thm)], [c_42, c_349])).
% 3.82/1.93  tff(c_455, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_450])).
% 3.82/1.93  tff(c_462, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_444, c_38, c_455])).
% 3.82/1.93  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_36, c_462])).
% 3.82/1.93  tff(c_465, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_112])).
% 3.82/1.93  tff(c_689, plain, (![B_111, C_112, A_113]: (k1_xboole_0=B_111 | v1_funct_2(C_112, A_113, B_111) | k1_relset_1(A_113, B_111, C_112)!=A_113 | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_111))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.82/1.93  tff(c_692, plain, (![C_112]: (k1_xboole_0='#skF_1' | v1_funct_2(C_112, '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', C_112)!='#skF_1' | ~m1_subset_1(C_112, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_465, c_689])).
% 3.82/1.93  tff(c_705, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_692])).
% 3.82/1.93  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.93  tff(c_473, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_465, c_10])).
% 3.82/1.93  tff(c_483, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_473])).
% 3.82/1.93  tff(c_719, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_705, c_483])).
% 3.82/1.93  tff(c_722, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_705, c_12])).
% 3.82/1.93  tff(c_759, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_722, c_465])).
% 3.82/1.93  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_719, c_759])).
% 3.82/1.93  tff(c_763, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_692])).
% 3.82/1.93  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.93  tff(c_861, plain, (![D_130, C_131, B_132, A_133]: (k1_funct_1(k2_funct_1(D_130), k1_funct_1(D_130, C_131))=C_131 | k1_xboole_0=B_132 | ~r2_hidden(C_131, A_133) | ~v2_funct_1(D_130) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(D_130, A_133, B_132) | ~v1_funct_1(D_130))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.93  tff(c_889, plain, (![D_135, B_136]: (k1_funct_1(k2_funct_1(D_135), k1_funct_1(D_135, '#skF_4'))='#skF_4' | k1_xboole_0=B_136 | ~v2_funct_1(D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_136))) | ~v1_funct_2(D_135, '#skF_1', B_136) | ~v1_funct_1(D_135))), inference(resolution, [status(thm)], [c_40, c_861])).
% 3.82/1.93  tff(c_1093, plain, (![A_151, B_152]: (k1_funct_1(k2_funct_1(A_151), k1_funct_1(A_151, '#skF_4'))='#skF_4' | k1_xboole_0=B_152 | ~v2_funct_1(A_151) | ~v1_funct_2(A_151, '#skF_1', B_152) | ~v1_funct_1(A_151) | ~r1_tarski(A_151, k2_zfmisc_1('#skF_1', B_152)))), inference(resolution, [status(thm)], [c_18, c_889])).
% 3.82/1.93  tff(c_1095, plain, (![A_151]: (k1_funct_1(k2_funct_1(A_151), k1_funct_1(A_151, '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1(A_151) | ~v1_funct_2(A_151, '#skF_1', '#skF_1') | ~v1_funct_1(A_151) | ~r1_tarski(A_151, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_465, c_1093])).
% 3.82/1.93  tff(c_1110, plain, (![A_153]: (k1_funct_1(k2_funct_1(A_153), k1_funct_1(A_153, '#skF_4'))='#skF_4' | ~v2_funct_1(A_153) | ~v1_funct_2(A_153, '#skF_1', '#skF_1') | ~v1_funct_1(A_153) | ~r1_tarski(A_153, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_763, c_1095])).
% 3.82/1.93  tff(c_468, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_46])).
% 3.82/1.93  tff(c_1033, plain, (![D_146, B_147]: (k1_funct_1(k2_funct_1(D_146), k1_funct_1(D_146, '#skF_3'))='#skF_3' | k1_xboole_0=B_147 | ~v2_funct_1(D_146) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_147))) | ~v1_funct_2(D_146, '#skF_1', B_147) | ~v1_funct_1(D_146))), inference(resolution, [status(thm)], [c_42, c_861])).
% 3.82/1.93  tff(c_1035, plain, (![D_146]: (k1_funct_1(k2_funct_1(D_146), k1_funct_1(D_146, '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1(D_146) | ~m1_subset_1(D_146, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_146, '#skF_1', '#skF_1') | ~v1_funct_1(D_146))), inference(superposition, [status(thm), theory('equality')], [c_465, c_1033])).
% 3.82/1.93  tff(c_1075, plain, (![D_150]: (k1_funct_1(k2_funct_1(D_150), k1_funct_1(D_150, '#skF_3'))='#skF_3' | ~v2_funct_1(D_150) | ~m1_subset_1(D_150, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_150, '#skF_1', '#skF_1') | ~v1_funct_1(D_150))), inference(negUnitSimplification, [status(thm)], [c_763, c_1035])).
% 3.82/1.93  tff(c_1084, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1075])).
% 3.82/1.93  tff(c_1088, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_468, c_44, c_1084])).
% 3.82/1.93  tff(c_1116, plain, ('#skF_3'='#skF_4' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1110, c_1088])).
% 3.82/1.93  tff(c_1125, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50, c_48, c_44, c_1116])).
% 3.82/1.93  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1125])).
% 3.82/1.93  tff(c_1129, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_473])).
% 3.82/1.93  tff(c_1128, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_473])).
% 3.82/1.93  tff(c_1146, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1129, c_1128])).
% 3.82/1.93  tff(c_1147, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_1146])).
% 3.82/1.93  tff(c_1156, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_50])).
% 3.82/1.93  tff(c_1151, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1147, c_468])).
% 3.82/1.93  tff(c_1155, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_44])).
% 3.82/1.93  tff(c_1153, plain, (k1_funct_1('#skF_1', '#skF_3')=k1_funct_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1147, c_38])).
% 3.82/1.93  tff(c_1134, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_8])).
% 3.82/1.93  tff(c_1149, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1134])).
% 3.82/1.93  tff(c_1198, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.93  tff(c_1317, plain, (![A_178, B_179, A_180]: (k1_relset_1(A_178, B_179, A_180)=k1_relat_1(A_180) | ~r1_tarski(A_180, k2_zfmisc_1(A_178, B_179)))), inference(resolution, [status(thm)], [c_18, c_1198])).
% 3.82/1.93  tff(c_1332, plain, (![A_178, B_179]: (k1_relset_1(A_178, B_179, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_1149, c_1317])).
% 3.82/1.93  tff(c_1154, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_48])).
% 3.82/1.93  tff(c_1150, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1129])).
% 3.82/1.93  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.93  tff(c_30, plain, (![B_12, C_13]: (k1_relset_1(k1_xboole_0, B_12, C_13)=k1_xboole_0 | ~v1_funct_2(C_13, k1_xboole_0, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.82/1.93  tff(c_51, plain, (![B_12, C_13]: (k1_relset_1(k1_xboole_0, B_12, C_13)=k1_xboole_0 | ~v1_funct_2(C_13, k1_xboole_0, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 3.82/1.93  tff(c_1371, plain, (![B_187, C_188]: (k1_relset_1('#skF_1', B_187, C_188)='#skF_1' | ~v1_funct_2(C_188, '#skF_1', B_187) | ~m1_subset_1(C_188, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_1150, c_1150, c_51])).
% 3.82/1.93  tff(c_1376, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1154, c_1371])).
% 3.82/1.93  tff(c_1383, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_1332, c_1376])).
% 3.82/1.93  tff(c_26, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.82/1.93  tff(c_52, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 3.82/1.93  tff(c_1361, plain, (![C_185, B_186]: (v1_funct_2(C_185, '#skF_1', B_186) | k1_relset_1('#skF_1', B_186, C_185)!='#skF_1' | ~m1_subset_1(C_185, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_1150, c_1150, c_52])).
% 3.82/1.93  tff(c_1363, plain, (![B_186]: (v1_funct_2('#skF_1', '#skF_1', B_186) | k1_relset_1('#skF_1', B_186, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_1151, c_1361])).
% 3.82/1.93  tff(c_1368, plain, (![B_186]: (v1_funct_2('#skF_1', '#skF_1', B_186) | k1_relat_1('#skF_1')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1363])).
% 3.82/1.93  tff(c_1397, plain, (![B_186]: (v1_funct_2('#skF_1', '#skF_1', B_186))), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1368])).
% 3.82/1.93  tff(c_1133, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1129, c_14])).
% 3.82/1.93  tff(c_1169, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1147, c_1133])).
% 3.82/1.93  tff(c_34, plain, (![D_17, C_16, B_15, A_14]: (k1_funct_1(k2_funct_1(D_17), k1_funct_1(D_17, C_16))=C_16 | k1_xboole_0=B_15 | ~r2_hidden(C_16, A_14) | ~v2_funct_1(D_17) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_17, A_14, B_15) | ~v1_funct_1(D_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.93  tff(c_1507, plain, (![D_207, C_208, B_209, A_210]: (k1_funct_1(k2_funct_1(D_207), k1_funct_1(D_207, C_208))=C_208 | B_209='#skF_1' | ~r2_hidden(C_208, A_210) | ~v2_funct_1(D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_2(D_207, A_210, B_209) | ~v1_funct_1(D_207))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_34])).
% 3.82/1.93  tff(c_1511, plain, (![D_207, B_209]: (k1_funct_1(k2_funct_1(D_207), k1_funct_1(D_207, '#skF_3'))='#skF_3' | B_209='#skF_1' | ~v2_funct_1(D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_209))) | ~v1_funct_2(D_207, '#skF_1', B_209) | ~v1_funct_1(D_207))), inference(resolution, [status(thm)], [c_42, c_1507])).
% 3.82/1.93  tff(c_1580, plain, (![D_218, B_219]: (k1_funct_1(k2_funct_1(D_218), k1_funct_1(D_218, '#skF_3'))='#skF_3' | B_219='#skF_1' | ~v2_funct_1(D_218) | ~m1_subset_1(D_218, k1_zfmisc_1('#skF_1')) | ~v1_funct_2(D_218, '#skF_1', B_219) | ~v1_funct_1(D_218))), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_1511])).
% 3.82/1.93  tff(c_1590, plain, (![B_186]: (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_3'))='#skF_3' | B_186='#skF_1' | ~v2_funct_1('#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1397, c_1580])).
% 3.82/1.93  tff(c_1603, plain, (![B_186]: (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_3' | B_186='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1151, c_1155, c_1153, c_1590])).
% 3.82/1.93  tff(c_1608, plain, (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_3'), inference(splitLeft, [status(thm)], [c_1603])).
% 3.82/1.93  tff(c_1509, plain, (![D_207, B_209]: (k1_funct_1(k2_funct_1(D_207), k1_funct_1(D_207, '#skF_4'))='#skF_4' | B_209='#skF_1' | ~v2_funct_1(D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_209))) | ~v1_funct_2(D_207, '#skF_1', B_209) | ~v1_funct_1(D_207))), inference(resolution, [status(thm)], [c_40, c_1507])).
% 3.82/1.93  tff(c_1648, plain, (![D_222, B_223]: (k1_funct_1(k2_funct_1(D_222), k1_funct_1(D_222, '#skF_4'))='#skF_4' | B_223='#skF_1' | ~v2_funct_1(D_222) | ~m1_subset_1(D_222, k1_zfmisc_1('#skF_1')) | ~v1_funct_2(D_222, '#skF_1', B_223) | ~v1_funct_1(D_222))), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_1509])).
% 3.82/1.93  tff(c_1658, plain, (![B_186]: (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_4' | B_186='#skF_1' | ~v2_funct_1('#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1397, c_1648])).
% 3.82/1.93  tff(c_1673, plain, (![B_186]: ('#skF_3'='#skF_4' | B_186='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1151, c_1155, c_1608, c_1658])).
% 3.82/1.93  tff(c_1681, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_36, c_1673])).
% 3.82/1.93  tff(c_1674, plain, (![B_186]: (B_186='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_1673])).
% 3.82/1.93  tff(c_1773, plain, (![B_505]: (B_505='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1681, c_1674])).
% 3.82/1.93  tff(c_1785, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1773, c_1608])).
% 3.82/1.93  tff(c_1849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1785])).
% 3.82/1.93  tff(c_1881, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1603])).
% 3.82/1.93  tff(c_1850, plain, (![B_186]: (B_186='#skF_1')), inference(splitRight, [status(thm)], [c_1603])).
% 3.82/1.93  tff(c_1961, plain, (![B_1019]: (B_1019='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1881, c_1850])).
% 3.82/1.93  tff(c_2029, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1961, c_36])).
% 3.82/1.93  tff(c_2030, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1146])).
% 3.82/1.93  tff(c_2031, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_1146])).
% 3.82/1.93  tff(c_2046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2030, c_2031])).
% 3.82/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.93  
% 3.82/1.93  Inference rules
% 3.82/1.93  ----------------------
% 3.82/1.93  #Ref     : 0
% 3.82/1.93  #Sup     : 475
% 3.82/1.93  #Fact    : 0
% 3.82/1.93  #Define  : 0
% 3.82/1.93  #Split   : 12
% 3.82/1.93  #Chain   : 0
% 3.82/1.93  #Close   : 0
% 3.82/1.93  
% 3.82/1.93  Ordering : KBO
% 3.82/1.93  
% 3.82/1.93  Simplification rules
% 3.82/1.93  ----------------------
% 3.82/1.93  #Subsume      : 90
% 3.82/1.93  #Demod        : 457
% 3.82/1.93  #Tautology    : 206
% 3.82/1.93  #SimpNegUnit  : 28
% 3.82/1.93  #BackRed      : 72
% 3.82/1.93  
% 3.82/1.93  #Partial instantiations: 51
% 3.82/1.93  #Strategies tried      : 1
% 3.82/1.93  
% 3.82/1.93  Timing (in seconds)
% 3.82/1.93  ----------------------
% 3.82/1.94  Preprocessing        : 0.41
% 3.82/1.94  Parsing              : 0.22
% 3.82/1.94  CNF conversion       : 0.02
% 3.82/1.94  Main loop            : 0.56
% 3.82/1.94  Inferencing          : 0.21
% 3.82/1.94  Reduction            : 0.18
% 3.82/1.94  Demodulation         : 0.13
% 3.82/1.94  BG Simplification    : 0.03
% 3.82/1.94  Subsumption          : 0.11
% 3.82/1.94  Abstraction          : 0.03
% 3.82/1.94  MUC search           : 0.00
% 3.82/1.94  Cooper               : 0.00
% 3.82/1.94  Total                : 1.02
% 3.82/1.94  Index Insertion      : 0.00
% 3.82/1.94  Index Deletion       : 0.00
% 3.82/1.94  Index Matching       : 0.00
% 3.82/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
