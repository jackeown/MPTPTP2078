%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 482 expanded)
%              Number of leaves         :   34 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 980 expanded)
%              Number of equality atoms :   39 ( 173 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3194,plain,(
    ! [C_253,A_254,B_255] :
      ( m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ r1_tarski(k2_relat_1(C_253),B_255)
      | ~ r1_tarski(k1_relat_1(C_253),A_254)
      | ~ v1_relat_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_83,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_94,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_117,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_403,plain,(
    ! [B_94,A_95,C_96] :
      ( r1_tarski(B_94,k3_subset_1(A_95,C_96))
      | ~ r1_xboole_0(B_94,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_11] :
      ( r1_tarski(k3_subset_1(A_11,k2_subset_1(A_11)),k2_subset_1(A_11))
      | ~ m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_11] : r1_tarski(k3_subset_1(A_11,k2_subset_1(A_11)),k2_subset_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_67,plain,(
    ! [A_11] : r1_tarski(k3_subset_1(A_11,A_11),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_64])).

tff(c_101,plain,(
    ! [A_11] :
      ( k3_subset_1(A_11,A_11) = A_11
      | ~ r1_tarski(A_11,k3_subset_1(A_11,A_11)) ) ),
    inference(resolution,[status(thm)],[c_67,c_94])).

tff(c_432,plain,(
    ! [C_96] :
      ( k3_subset_1(C_96,C_96) = C_96
      | ~ r1_xboole_0(C_96,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(C_96)) ) ),
    inference(resolution,[status(thm)],[c_403,c_101])).

tff(c_466,plain,(
    ! [C_97] :
      ( k3_subset_1(C_97,C_97) = C_97
      | ~ r1_xboole_0(C_97,C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_432])).

tff(c_475,plain,(
    k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_466])).

tff(c_376,plain,(
    ! [C_91,A_92,B_93] :
      ( m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ r1_tarski(k2_relat_1(C_91),B_93)
      | ~ r1_tarski(k1_relat_1(C_91),A_92)
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_787,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ r1_tarski(k2_relat_1(C_124),B_123)
      | ~ r1_tarski(k1_relat_1(C_124),A_122)
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_376,c_30])).

tff(c_792,plain,(
    ! [A_122] :
      ( k1_relset_1(A_122,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_122)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_787])).

tff(c_801,plain,(
    ! [A_125] :
      ( k1_relset_1(A_125,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_792])).

tff(c_811,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_801])).

tff(c_32,plain,(
    ! [C_26,A_24,B_25] :
      ( m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ r1_tarski(k2_relat_1(C_26),B_25)
      | ~ r1_tarski(k1_relat_1(C_26),A_24)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_620,plain,(
    ! [B_102,C_103,A_104] :
      ( k1_xboole_0 = B_102
      | v1_funct_2(C_103,A_104,B_102)
      | k1_relset_1(A_104,B_102,C_103) != A_104
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2103,plain,(
    ! [B_186,C_187,A_188] :
      ( k1_xboole_0 = B_186
      | v1_funct_2(C_187,A_188,B_186)
      | k1_relset_1(A_188,B_186,C_187) != A_188
      | ~ r1_tarski(k2_relat_1(C_187),B_186)
      | ~ r1_tarski(k1_relat_1(C_187),A_188)
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_32,c_620])).

tff(c_2115,plain,(
    ! [A_188] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_188,'#skF_1')
      | k1_relset_1(A_188,'#skF_1','#skF_2') != A_188
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_188)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_2103])).

tff(c_2129,plain,(
    ! [A_188] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_188,'#skF_1')
      | k1_relset_1(A_188,'#skF_1','#skF_2') != A_188
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2115])).

tff(c_2658,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2129])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_984,plain,(
    ! [A_142,A_143,C_144,B_145] :
      ( r1_tarski(A_142,k3_subset_1(A_143,C_144))
      | ~ r1_tarski(A_142,B_145)
      | ~ r1_xboole_0(B_145,C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_143))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_403,c_10])).

tff(c_1016,plain,(
    ! [A_146,C_147] :
      ( r1_tarski(k2_relat_1('#skF_2'),k3_subset_1(A_146,C_147))
      | ~ r1_xboole_0('#skF_1',C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_146))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(A_146)) ) ),
    inference(resolution,[status(thm)],[c_54,c_984])).

tff(c_1054,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0)
    | ~ r1_xboole_0('#skF_1',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_1016])).

tff(c_1081,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_12,c_1054])).

tff(c_1105,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_2673,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2658,c_1105])).

tff(c_2705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2673])).

tff(c_2708,plain,(
    ! [A_202] :
      ( v1_funct_2('#skF_2',A_202,'#skF_1')
      | k1_relset_1(A_202,'#skF_1','#skF_2') != A_202
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_202) ) ),
    inference(splitRight,[status(thm)],[c_2129])).

tff(c_2720,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_2708])).

tff(c_2725,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_2720])).

tff(c_2727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_2725])).

tff(c_2728,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_26,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_43,A_11] :
      ( r1_tarski(A_43,A_11)
      | ~ r1_tarski(A_43,k3_subset_1(A_11,A_11)) ) ),
    inference(resolution,[status(thm)],[c_67,c_107])).

tff(c_436,plain,(
    ! [B_94,C_96] :
      ( r1_tarski(B_94,C_96)
      | ~ r1_xboole_0(B_94,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(C_96))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_96)) ) ),
    inference(resolution,[status(thm)],[c_403,c_114])).

tff(c_550,plain,(
    ! [B_99,C_100] :
      ( r1_tarski(B_99,C_100)
      | ~ r1_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(C_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_436])).

tff(c_559,plain,(
    ! [A_17] :
      ( r1_tarski(k1_xboole_0,A_17)
      | ~ r1_xboole_0(k1_xboole_0,A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_550])).

tff(c_570,plain,(
    ! [A_101] : r1_tarski(k1_xboole_0,A_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_559])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_619,plain,(
    ! [A_101] :
      ( k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_570,c_4])).

tff(c_2761,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2728,c_619])).

tff(c_118,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,'#skF_1')
      | ~ r1_tarski(A_46,k2_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_127,plain,(
    r1_tarski(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_118])).

tff(c_135,plain,
    ( k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_291,plain,(
    ~ r1_tarski('#skF_1',k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_2774,plain,(
    ~ r1_tarski('#skF_1',k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2761,c_2761,c_291])).

tff(c_2791,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_2774])).

tff(c_2729,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_463,plain,(
    ! [B_94,C_96] :
      ( r1_tarski(B_94,C_96)
      | ~ r1_xboole_0(B_94,C_96)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_436])).

tff(c_2859,plain,
    ( r1_tarski('#skF_1',k1_xboole_0)
    | ~ r1_xboole_0('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2729,c_463])).

tff(c_2867,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2859])).

tff(c_2869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2791,c_2867])).

tff(c_2870,plain,(
    k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_2901,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2870,c_67])).

tff(c_2913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_2901])).

tff(c_2914,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2922,plain,(
    ! [A_205] :
      ( v1_funct_2(A_205,k1_relat_1(A_205),k2_relat_1(A_205))
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2925,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_2922])).

tff(c_2927,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2925])).

tff(c_2929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_2927])).

tff(c_2930,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3214,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3194,c_2930])).

tff(c_3223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8,c_54,c_3214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/1.99  
% 5.40/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.00  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.40/2.00  
% 5.40/2.00  %Foreground sorts:
% 5.40/2.00  
% 5.40/2.00  
% 5.40/2.00  %Background operators:
% 5.40/2.00  
% 5.40/2.00  
% 5.40/2.00  %Foreground operators:
% 5.40/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.40/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.40/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.40/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.40/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.40/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.40/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.40/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.40/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.40/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.40/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.40/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.40/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.40/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.40/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.40/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.40/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.40/2.00  
% 5.52/2.02  tff(f_123, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.52/2.02  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.52/2.02  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.52/2.02  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.52/2.02  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.52/2.02  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.52/2.02  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.52/2.02  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 5.52/2.02  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 5.52/2.02  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.52/2.02  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.52/2.02  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.52/2.02  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.52/2.02  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.52/2.02  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.52/2.02  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.02  tff(c_54, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.52/2.02  tff(c_3194, plain, (![C_253, A_254, B_255]: (m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~r1_tarski(k2_relat_1(C_253), B_255) | ~r1_tarski(k1_relat_1(C_253), A_254) | ~v1_relat_1(C_253))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.52/2.02  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.52/2.02  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.52/2.02  tff(c_60, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 5.52/2.02  tff(c_83, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 5.52/2.02  tff(c_94, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.02  tff(c_102, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_94])).
% 5.52/2.02  tff(c_117, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_102])).
% 5.52/2.02  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.52/2.02  tff(c_84, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.52/2.02  tff(c_87, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_12, c_84])).
% 5.52/2.02  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.52/2.02  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.52/2.02  tff(c_65, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 5.52/2.02  tff(c_403, plain, (![B_94, A_95, C_96]: (r1_tarski(B_94, k3_subset_1(A_95, C_96)) | ~r1_xboole_0(B_94, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.52/2.02  tff(c_18, plain, (![A_11]: (r1_tarski(k3_subset_1(A_11, k2_subset_1(A_11)), k2_subset_1(A_11)) | ~m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.52/2.02  tff(c_64, plain, (![A_11]: (r1_tarski(k3_subset_1(A_11, k2_subset_1(A_11)), k2_subset_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 5.52/2.02  tff(c_67, plain, (![A_11]: (r1_tarski(k3_subset_1(A_11, A_11), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_64])).
% 5.52/2.02  tff(c_101, plain, (![A_11]: (k3_subset_1(A_11, A_11)=A_11 | ~r1_tarski(A_11, k3_subset_1(A_11, A_11)))), inference(resolution, [status(thm)], [c_67, c_94])).
% 5.52/2.02  tff(c_432, plain, (![C_96]: (k3_subset_1(C_96, C_96)=C_96 | ~r1_xboole_0(C_96, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(C_96)))), inference(resolution, [status(thm)], [c_403, c_101])).
% 5.52/2.02  tff(c_466, plain, (![C_97]: (k3_subset_1(C_97, C_97)=C_97 | ~r1_xboole_0(C_97, C_97))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_432])).
% 5.52/2.02  tff(c_475, plain, (k3_subset_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_466])).
% 5.52/2.02  tff(c_376, plain, (![C_91, A_92, B_93]: (m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~r1_tarski(k2_relat_1(C_91), B_93) | ~r1_tarski(k1_relat_1(C_91), A_92) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.52/2.02  tff(c_30, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.52/2.02  tff(c_787, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~r1_tarski(k2_relat_1(C_124), B_123) | ~r1_tarski(k1_relat_1(C_124), A_122) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_376, c_30])).
% 5.52/2.02  tff(c_792, plain, (![A_122]: (k1_relset_1(A_122, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_122) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_787])).
% 5.52/2.02  tff(c_801, plain, (![A_125]: (k1_relset_1(A_125, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_125))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_792])).
% 5.52/2.02  tff(c_811, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_801])).
% 5.52/2.02  tff(c_32, plain, (![C_26, A_24, B_25]: (m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~r1_tarski(k2_relat_1(C_26), B_25) | ~r1_tarski(k1_relat_1(C_26), A_24) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.52/2.02  tff(c_620, plain, (![B_102, C_103, A_104]: (k1_xboole_0=B_102 | v1_funct_2(C_103, A_104, B_102) | k1_relset_1(A_104, B_102, C_103)!=A_104 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.52/2.02  tff(c_2103, plain, (![B_186, C_187, A_188]: (k1_xboole_0=B_186 | v1_funct_2(C_187, A_188, B_186) | k1_relset_1(A_188, B_186, C_187)!=A_188 | ~r1_tarski(k2_relat_1(C_187), B_186) | ~r1_tarski(k1_relat_1(C_187), A_188) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_32, c_620])).
% 5.52/2.02  tff(c_2115, plain, (![A_188]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_188, '#skF_1') | k1_relset_1(A_188, '#skF_1', '#skF_2')!=A_188 | ~r1_tarski(k1_relat_1('#skF_2'), A_188) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_2103])).
% 5.52/2.02  tff(c_2129, plain, (![A_188]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_188, '#skF_1') | k1_relset_1(A_188, '#skF_1', '#skF_2')!=A_188 | ~r1_tarski(k1_relat_1('#skF_2'), A_188))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2115])).
% 5.52/2.02  tff(c_2658, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2129])).
% 5.52/2.02  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/2.02  tff(c_984, plain, (![A_142, A_143, C_144, B_145]: (r1_tarski(A_142, k3_subset_1(A_143, C_144)) | ~r1_tarski(A_142, B_145) | ~r1_xboole_0(B_145, C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(A_143)) | ~m1_subset_1(B_145, k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_403, c_10])).
% 5.52/2.02  tff(c_1016, plain, (![A_146, C_147]: (r1_tarski(k2_relat_1('#skF_2'), k3_subset_1(A_146, C_147)) | ~r1_xboole_0('#skF_1', C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(A_146)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(A_146)))), inference(resolution, [status(thm)], [c_54, c_984])).
% 5.52/2.02  tff(c_1054, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0) | ~r1_xboole_0('#skF_1', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_475, c_1016])).
% 5.52/2.02  tff(c_1081, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_12, c_1054])).
% 5.52/2.02  tff(c_1105, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1081])).
% 5.52/2.02  tff(c_2673, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2658, c_1105])).
% 5.52/2.02  tff(c_2705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_2673])).
% 5.52/2.02  tff(c_2708, plain, (![A_202]: (v1_funct_2('#skF_2', A_202, '#skF_1') | k1_relset_1(A_202, '#skF_1', '#skF_2')!=A_202 | ~r1_tarski(k1_relat_1('#skF_2'), A_202))), inference(splitRight, [status(thm)], [c_2129])).
% 5.52/2.02  tff(c_2720, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_2708])).
% 5.52/2.02  tff(c_2725, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_2720])).
% 5.52/2.02  tff(c_2727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_2725])).
% 5.52/2.02  tff(c_2728, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1081])).
% 5.52/2.02  tff(c_26, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.02  tff(c_107, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/2.02  tff(c_114, plain, (![A_43, A_11]: (r1_tarski(A_43, A_11) | ~r1_tarski(A_43, k3_subset_1(A_11, A_11)))), inference(resolution, [status(thm)], [c_67, c_107])).
% 5.52/2.02  tff(c_436, plain, (![B_94, C_96]: (r1_tarski(B_94, C_96) | ~r1_xboole_0(B_94, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(C_96)) | ~m1_subset_1(B_94, k1_zfmisc_1(C_96)))), inference(resolution, [status(thm)], [c_403, c_114])).
% 5.52/2.02  tff(c_550, plain, (![B_99, C_100]: (r1_tarski(B_99, C_100) | ~r1_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(C_100)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_436])).
% 5.52/2.02  tff(c_559, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17) | ~r1_xboole_0(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_26, c_550])).
% 5.52/2.02  tff(c_570, plain, (![A_101]: (r1_tarski(k1_xboole_0, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_559])).
% 5.52/2.02  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.02  tff(c_619, plain, (![A_101]: (k1_xboole_0=A_101 | ~r1_tarski(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_570, c_4])).
% 5.52/2.02  tff(c_2761, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2728, c_619])).
% 5.52/2.02  tff(c_118, plain, (![A_46]: (r1_tarski(A_46, '#skF_1') | ~r1_tarski(A_46, k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_107])).
% 5.52/2.02  tff(c_127, plain, (r1_tarski(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_67, c_118])).
% 5.52/2.02  tff(c_135, plain, (k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_127, c_4])).
% 5.52/2.02  tff(c_291, plain, (~r1_tarski('#skF_1', k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_135])).
% 5.52/2.02  tff(c_2774, plain, (~r1_tarski('#skF_1', k3_subset_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2761, c_2761, c_291])).
% 5.52/2.02  tff(c_2791, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_475, c_2774])).
% 5.52/2.02  tff(c_2729, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1081])).
% 5.52/2.02  tff(c_463, plain, (![B_94, C_96]: (r1_tarski(B_94, C_96) | ~r1_xboole_0(B_94, C_96) | ~m1_subset_1(B_94, k1_zfmisc_1(C_96)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_436])).
% 5.52/2.02  tff(c_2859, plain, (r1_tarski('#skF_1', k1_xboole_0) | ~r1_xboole_0('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_2729, c_463])).
% 5.52/2.02  tff(c_2867, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2859])).
% 5.52/2.02  tff(c_2869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2791, c_2867])).
% 5.52/2.02  tff(c_2870, plain, (k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_135])).
% 5.52/2.02  tff(c_2901, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2870, c_67])).
% 5.52/2.02  tff(c_2913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_2901])).
% 5.52/2.02  tff(c_2914, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_102])).
% 5.52/2.02  tff(c_2922, plain, (![A_205]: (v1_funct_2(A_205, k1_relat_1(A_205), k2_relat_1(A_205)) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.52/2.02  tff(c_2925, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2914, c_2922])).
% 5.52/2.02  tff(c_2927, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2925])).
% 5.52/2.02  tff(c_2929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_2927])).
% 5.52/2.02  tff(c_2930, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 5.52/2.02  tff(c_3214, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3194, c_2930])).
% 5.52/2.02  tff(c_3223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_8, c_54, c_3214])).
% 5.52/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.02  
% 5.52/2.02  Inference rules
% 5.52/2.02  ----------------------
% 5.52/2.02  #Ref     : 0
% 5.52/2.02  #Sup     : 617
% 5.52/2.02  #Fact    : 0
% 5.52/2.02  #Define  : 0
% 5.52/2.02  #Split   : 15
% 5.52/2.02  #Chain   : 0
% 5.52/2.02  #Close   : 0
% 5.52/2.02  
% 5.52/2.02  Ordering : KBO
% 5.52/2.02  
% 5.52/2.02  Simplification rules
% 5.52/2.02  ----------------------
% 5.52/2.02  #Subsume      : 110
% 5.52/2.02  #Demod        : 558
% 5.52/2.02  #Tautology    : 177
% 5.52/2.02  #SimpNegUnit  : 8
% 5.52/2.02  #BackRed      : 63
% 5.52/2.02  
% 5.52/2.02  #Partial instantiations: 0
% 5.52/2.02  #Strategies tried      : 1
% 5.52/2.02  
% 5.52/2.02  Timing (in seconds)
% 5.52/2.02  ----------------------
% 5.52/2.02  Preprocessing        : 0.36
% 5.52/2.02  Parsing              : 0.19
% 5.52/2.02  CNF conversion       : 0.02
% 5.52/2.02  Main loop            : 0.87
% 5.56/2.02  Inferencing          : 0.26
% 5.56/2.02  Reduction            : 0.29
% 5.56/2.02  Demodulation         : 0.21
% 5.56/2.02  BG Simplification    : 0.04
% 5.56/2.02  Subsumption          : 0.21
% 5.56/2.02  Abstraction          : 0.05
% 5.56/2.02  MUC search           : 0.00
% 5.56/2.02  Cooper               : 0.00
% 5.56/2.02  Total                : 1.27
% 5.56/2.02  Index Insertion      : 0.00
% 5.56/2.02  Index Deletion       : 0.00
% 5.56/2.02  Index Matching       : 0.00
% 5.56/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
