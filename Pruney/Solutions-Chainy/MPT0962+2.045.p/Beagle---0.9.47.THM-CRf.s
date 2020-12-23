%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 283 expanded)
%              Number of leaves         :   26 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 ( 711 expanded)
%              Number of equality atoms :   61 ( 198 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1297,plain,(
    ! [C_236,A_237,B_238] :
      ( m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ r1_tarski(k2_relat_1(C_236),B_238)
      | ~ r1_tarski(k1_relat_1(C_236),A_237)
      | ~ v1_relat_1(C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_64,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_242,plain,(
    ! [C_65,A_66,B_67] :
      ( m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ r1_tarski(k2_relat_1(C_65),B_67)
      | ~ r1_tarski(k1_relat_1(C_65),A_66)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_280,plain,(
    ! [C_69,A_70,B_71] :
      ( r1_tarski(C_69,k2_zfmisc_1(A_70,B_71))
      | ~ r1_tarski(k2_relat_1(C_69),B_71)
      | ~ r1_tarski(k1_relat_1(C_69),A_70)
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_242,c_10])).

tff(c_282,plain,(
    ! [A_70] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_70,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_70)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_280])).

tff(c_294,plain,(
    ! [A_72] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_72,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_282])).

tff(c_299,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_294])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [A_37,B_38,A_4] :
      ( k1_relset_1(A_37,B_38,A_4) = k1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_37,B_38)) ) ),
    inference(resolution,[status(thm)],[c_12,c_122])).

tff(c_305,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_299,c_131])).

tff(c_311,plain,(
    ! [B_73,C_74,A_75] :
      ( k1_xboole_0 = B_73
      | v1_funct_2(C_74,A_75,B_73)
      | k1_relset_1(A_75,B_73,C_74) != A_75
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_433,plain,(
    ! [B_88,A_89,A_90] :
      ( k1_xboole_0 = B_88
      | v1_funct_2(A_89,A_90,B_88)
      | k1_relset_1(A_90,B_88,A_89) != A_90
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_90,B_88)) ) ),
    inference(resolution,[status(thm)],[c_12,c_311])).

tff(c_439,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_299,c_433])).

tff(c_451,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_439])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_451])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_499,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_84])).

tff(c_87,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_113])).

tff(c_514,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_71,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_86,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_516,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_86])).

tff(c_665,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ r1_tarski(k2_relat_1(C_128),B_130)
      | ~ r1_tarski(k1_relat_1(C_128),A_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_710,plain,(
    ! [C_136,A_137,B_138] :
      ( r1_tarski(C_136,k2_zfmisc_1(A_137,B_138))
      | ~ r1_tarski(k2_relat_1(C_136),B_138)
      | ~ r1_tarski(k1_relat_1(C_136),A_137)
      | ~ v1_relat_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_665,c_10])).

tff(c_723,plain,(
    ! [C_139,A_140] :
      ( r1_tarski(C_139,k2_zfmisc_1(A_140,k2_relat_1(C_139)))
      | ~ r1_tarski(k1_relat_1(C_139),A_140)
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_710])).

tff(c_742,plain,(
    ! [A_140] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_140,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_140)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_723])).

tff(c_755,plain,(
    ! [A_141] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_141,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_742])).

tff(c_765,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_755])).

tff(c_533,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_542,plain,(
    ! [A_102,B_103,A_4] :
      ( k1_relset_1(A_102,B_103,A_4) = k1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_12,c_533])).

tff(c_771,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_765,c_542])).

tff(c_692,plain,(
    ! [B_131,C_132,A_133] :
      ( k1_xboole_0 = B_131
      | v1_funct_2(C_132,A_133,B_131)
      | k1_relset_1(A_133,B_131,C_132) != A_133
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_855,plain,(
    ! [B_151,A_152,A_153] :
      ( k1_xboole_0 = B_151
      | v1_funct_2(A_152,A_153,B_151)
      | k1_relset_1(A_153,B_151,A_152) != A_153
      | ~ r1_tarski(A_152,k2_zfmisc_1(A_153,B_151)) ) ),
    inference(resolution,[status(thm)],[c_12,c_692])).

tff(c_861,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_765,c_855])).

tff(c_876,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_861])).

tff(c_878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_516,c_876])).

tff(c_879,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_887,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_18])).

tff(c_65,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_70,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_883,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_70])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_883])).

tff(c_909,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_910,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_920,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_910])).

tff(c_913,plain,(
    ! [A_3] : m1_subset_1('#skF_2',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_8])).

tff(c_991,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_995,plain,(
    ! [A_170,B_171] : k1_relset_1(A_170,B_171,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_913,c_991])).

tff(c_1001,plain,(
    ! [A_170,B_171] : k1_relset_1(A_170,B_171,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_995])).

tff(c_32,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1085,plain,(
    ! [C_192,B_193] :
      ( v1_funct_2(C_192,'#skF_2',B_193)
      | k1_relset_1('#skF_2',B_193,C_192) != '#skF_2'
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_193))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_909,c_909,c_909,c_32])).

tff(c_1089,plain,(
    ! [B_193] :
      ( v1_funct_2('#skF_2','#skF_2',B_193)
      | k1_relset_1('#skF_2',B_193,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_913,c_1085])).

tff(c_1096,plain,(
    ! [B_193] : v1_funct_2('#skF_2','#skF_2',B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1089])).

tff(c_921,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_64])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_921])).

tff(c_1101,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1320,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1297,c_1101])).

tff(c_1330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_42,c_1320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.50  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.12/1.50  
% 3.12/1.50  %Foreground sorts:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Background operators:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Foreground operators:
% 3.12/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.50  
% 3.48/1.52  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.48/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.52  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.48/1.52  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.52  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.48/1.52  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.48/1.52  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.48/1.52  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.48/1.52  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.48/1.52  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.52  tff(c_42, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.52  tff(c_1297, plain, (![C_236, A_237, B_238]: (m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~r1_tarski(k2_relat_1(C_236), B_238) | ~r1_tarski(k1_relat_1(C_236), A_237) | ~v1_relat_1(C_236))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.52  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.52  tff(c_40, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.52  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 3.48/1.52  tff(c_64, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.48/1.52  tff(c_242, plain, (![C_65, A_66, B_67]: (m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~r1_tarski(k2_relat_1(C_65), B_67) | ~r1_tarski(k1_relat_1(C_65), A_66) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.52  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.52  tff(c_280, plain, (![C_69, A_70, B_71]: (r1_tarski(C_69, k2_zfmisc_1(A_70, B_71)) | ~r1_tarski(k2_relat_1(C_69), B_71) | ~r1_tarski(k1_relat_1(C_69), A_70) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_242, c_10])).
% 3.48/1.52  tff(c_282, plain, (![A_70]: (r1_tarski('#skF_2', k2_zfmisc_1(A_70, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_70) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_280])).
% 3.48/1.52  tff(c_294, plain, (![A_72]: (r1_tarski('#skF_2', k2_zfmisc_1(A_72, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_282])).
% 3.48/1.52  tff(c_299, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_294])).
% 3.48/1.52  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.52  tff(c_122, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.52  tff(c_131, plain, (![A_37, B_38, A_4]: (k1_relset_1(A_37, B_38, A_4)=k1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_37, B_38)))), inference(resolution, [status(thm)], [c_12, c_122])).
% 3.48/1.52  tff(c_305, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_299, c_131])).
% 3.48/1.52  tff(c_311, plain, (![B_73, C_74, A_75]: (k1_xboole_0=B_73 | v1_funct_2(C_74, A_75, B_73) | k1_relset_1(A_75, B_73, C_74)!=A_75 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_73))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.52  tff(c_433, plain, (![B_88, A_89, A_90]: (k1_xboole_0=B_88 | v1_funct_2(A_89, A_90, B_88) | k1_relset_1(A_90, B_88, A_89)!=A_90 | ~r1_tarski(A_89, k2_zfmisc_1(A_90, B_88)))), inference(resolution, [status(thm)], [c_12, c_311])).
% 3.48/1.52  tff(c_439, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_299, c_433])).
% 3.48/1.52  tff(c_451, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_439])).
% 3.48/1.52  tff(c_452, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_451])).
% 3.48/1.52  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.52  tff(c_76, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.52  tff(c_84, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_76])).
% 3.48/1.52  tff(c_499, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_84])).
% 3.48/1.52  tff(c_87, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.52  tff(c_95, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_87])).
% 3.48/1.52  tff(c_113, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_95])).
% 3.48/1.52  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_499, c_113])).
% 3.48/1.52  tff(c_514, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_95])).
% 3.48/1.52  tff(c_71, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.52  tff(c_75, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_71])).
% 3.48/1.52  tff(c_86, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_75])).
% 3.48/1.52  tff(c_516, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_86])).
% 3.48/1.52  tff(c_665, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~r1_tarski(k2_relat_1(C_128), B_130) | ~r1_tarski(k1_relat_1(C_128), A_129) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.52  tff(c_710, plain, (![C_136, A_137, B_138]: (r1_tarski(C_136, k2_zfmisc_1(A_137, B_138)) | ~r1_tarski(k2_relat_1(C_136), B_138) | ~r1_tarski(k1_relat_1(C_136), A_137) | ~v1_relat_1(C_136))), inference(resolution, [status(thm)], [c_665, c_10])).
% 3.48/1.52  tff(c_723, plain, (![C_139, A_140]: (r1_tarski(C_139, k2_zfmisc_1(A_140, k2_relat_1(C_139))) | ~r1_tarski(k1_relat_1(C_139), A_140) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_6, c_710])).
% 3.48/1.52  tff(c_742, plain, (![A_140]: (r1_tarski('#skF_2', k2_zfmisc_1(A_140, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_140) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_514, c_723])).
% 3.48/1.52  tff(c_755, plain, (![A_141]: (r1_tarski('#skF_2', k2_zfmisc_1(A_141, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_141))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_742])).
% 3.48/1.52  tff(c_765, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_755])).
% 3.48/1.52  tff(c_533, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.52  tff(c_542, plain, (![A_102, B_103, A_4]: (k1_relset_1(A_102, B_103, A_4)=k1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_102, B_103)))), inference(resolution, [status(thm)], [c_12, c_533])).
% 3.48/1.52  tff(c_771, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_765, c_542])).
% 3.48/1.52  tff(c_692, plain, (![B_131, C_132, A_133]: (k1_xboole_0=B_131 | v1_funct_2(C_132, A_133, B_131) | k1_relset_1(A_133, B_131, C_132)!=A_133 | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_131))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.52  tff(c_855, plain, (![B_151, A_152, A_153]: (k1_xboole_0=B_151 | v1_funct_2(A_152, A_153, B_151) | k1_relset_1(A_153, B_151, A_152)!=A_153 | ~r1_tarski(A_152, k2_zfmisc_1(A_153, B_151)))), inference(resolution, [status(thm)], [c_12, c_692])).
% 3.48/1.52  tff(c_861, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_765, c_855])).
% 3.48/1.52  tff(c_876, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_861])).
% 3.48/1.52  tff(c_878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_516, c_876])).
% 3.48/1.52  tff(c_879, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_75])).
% 3.48/1.52  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.52  tff(c_887, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_18])).
% 3.48/1.52  tff(c_65, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.52  tff(c_69, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_65])).
% 3.48/1.52  tff(c_70, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_69])).
% 3.48/1.52  tff(c_883, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_70])).
% 3.48/1.52  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_887, c_883])).
% 3.48/1.52  tff(c_909, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_69])).
% 3.48/1.52  tff(c_910, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_69])).
% 3.48/1.52  tff(c_920, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_909, c_910])).
% 3.48/1.52  tff(c_913, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_8])).
% 3.48/1.52  tff(c_991, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.52  tff(c_995, plain, (![A_170, B_171]: (k1_relset_1(A_170, B_171, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_913, c_991])).
% 3.48/1.52  tff(c_1001, plain, (![A_170, B_171]: (k1_relset_1(A_170, B_171, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_920, c_995])).
% 3.48/1.52  tff(c_32, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.52  tff(c_1085, plain, (![C_192, B_193]: (v1_funct_2(C_192, '#skF_2', B_193) | k1_relset_1('#skF_2', B_193, C_192)!='#skF_2' | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_193))))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_909, c_909, c_909, c_32])).
% 3.48/1.52  tff(c_1089, plain, (![B_193]: (v1_funct_2('#skF_2', '#skF_2', B_193) | k1_relset_1('#skF_2', B_193, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_913, c_1085])).
% 3.48/1.52  tff(c_1096, plain, (![B_193]: (v1_funct_2('#skF_2', '#skF_2', B_193))), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1089])).
% 3.48/1.52  tff(c_921, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_920, c_64])).
% 3.48/1.52  tff(c_1100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1096, c_921])).
% 3.48/1.52  tff(c_1101, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_48])).
% 3.48/1.52  tff(c_1320, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1297, c_1101])).
% 3.48/1.52  tff(c_1330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_42, c_1320])).
% 3.48/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.52  
% 3.48/1.52  Inference rules
% 3.48/1.52  ----------------------
% 3.48/1.52  #Ref     : 0
% 3.48/1.52  #Sup     : 238
% 3.48/1.52  #Fact    : 0
% 3.48/1.52  #Define  : 0
% 3.48/1.52  #Split   : 10
% 3.48/1.52  #Chain   : 0
% 3.48/1.52  #Close   : 0
% 3.48/1.52  
% 3.48/1.52  Ordering : KBO
% 3.48/1.52  
% 3.48/1.52  Simplification rules
% 3.48/1.52  ----------------------
% 3.48/1.52  #Subsume      : 3
% 3.48/1.52  #Demod        : 218
% 3.48/1.52  #Tautology    : 111
% 3.48/1.52  #SimpNegUnit  : 3
% 3.48/1.52  #BackRed      : 49
% 3.48/1.52  
% 3.48/1.52  #Partial instantiations: 0
% 3.48/1.52  #Strategies tried      : 1
% 3.48/1.52  
% 3.48/1.52  Timing (in seconds)
% 3.48/1.52  ----------------------
% 3.48/1.52  Preprocessing        : 0.31
% 3.48/1.52  Parsing              : 0.17
% 3.48/1.52  CNF conversion       : 0.02
% 3.48/1.52  Main loop            : 0.44
% 3.48/1.52  Inferencing          : 0.16
% 3.48/1.52  Reduction            : 0.13
% 3.48/1.52  Demodulation         : 0.09
% 3.48/1.52  BG Simplification    : 0.02
% 3.48/1.52  Subsumption          : 0.09
% 3.48/1.52  Abstraction          : 0.02
% 3.48/1.52  MUC search           : 0.00
% 3.48/1.52  Cooper               : 0.00
% 3.48/1.52  Total                : 0.79
% 3.48/1.52  Index Insertion      : 0.00
% 3.48/1.52  Index Deletion       : 0.00
% 3.48/1.52  Index Matching       : 0.00
% 3.48/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
