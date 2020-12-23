%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 588 expanded)
%              Number of leaves         :   22 ( 197 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 (1517 expanded)
%              Number of equality atoms :   54 ( 677 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_77,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_261,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ r1_tarski(k2_relat_1(C_84),B_86)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_157,plain,(
    ! [C_45,A_46,B_47] :
      ( m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ r1_tarski(k2_relat_1(C_45),B_47)
      | ~ r1_tarski(k1_relat_1(C_45),A_46)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_187,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ r1_tarski(k2_relat_1(C_58),B_57)
      | ~ r1_tarski(k1_relat_1(C_58),A_56)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_157,c_20])).

tff(c_192,plain,(
    ! [A_59,C_60] :
      ( k1_relset_1(A_59,k2_relat_1(C_60),C_60) = k1_relat_1(C_60)
      | ~ r1_tarski(k1_relat_1(C_60),A_59)
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_196,plain,(
    ! [C_60] :
      ( k1_relset_1(k1_relat_1(C_60),k2_relat_1(C_60),C_60) = k1_relat_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_77,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_91,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_22,plain,(
    ! [C_13,A_11,B_12] :
      ( m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ r1_tarski(k2_relat_1(C_13),B_12)
      | ~ r1_tarski(k1_relat_1(C_13),A_11)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_168,plain,(
    ! [B_48,C_49,A_50] :
      ( k1_xboole_0 = B_48
      | v1_funct_2(C_49,A_50,B_48)
      | k1_relset_1(A_50,B_48,C_49) != A_50
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_219,plain,(
    ! [B_68,C_69,A_70] :
      ( k1_xboole_0 = B_68
      | v1_funct_2(C_69,A_70,B_68)
      | k1_relset_1(A_70,B_68,C_69) != A_70
      | ~ r1_tarski(k2_relat_1(C_69),B_68)
      | ~ r1_tarski(k1_relat_1(C_69),A_70)
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_22,c_168])).

tff(c_224,plain,(
    ! [C_71,A_72] :
      ( k2_relat_1(C_71) = k1_xboole_0
      | v1_funct_2(C_71,A_72,k2_relat_1(C_71))
      | k1_relset_1(A_72,k2_relat_1(C_71),C_71) != A_72
      | ~ r1_tarski(k1_relat_1(C_71),A_72)
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_144,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_232,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_224,c_144])).

tff(c_239,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_232])).

tff(c_240,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_239])).

tff(c_243,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_243])).

tff(c_248,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_267,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_261,c_248])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_6,c_267])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_14,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_388,plain,(
    ! [A_14] :
      ( v1_funct_2('#skF_1',A_14,'#skF_1')
      | A_14 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_279,c_279,c_279,c_45])).

tff(c_389,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_280,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_290,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_280])).

tff(c_283,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_10])).

tff(c_401,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ r1_tarski(k2_relat_1(C_108),B_110)
      | ~ r1_tarski(k1_relat_1(C_108),A_109)
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_416,plain,(
    ! [C_115,A_116] :
      ( m1_subset_1(C_115,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(C_115),'#skF_1')
      | ~ r1_tarski(k1_relat_1(C_115),A_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_401])).

tff(c_418,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski('#skF_1','#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_116)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_416])).

tff(c_420,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_418])).

tff(c_422,plain,(
    ! [A_117] : ~ r1_tarski(k1_relat_1('#skF_1'),A_117) ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_420])).

tff(c_427,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_422])).

tff(c_437,plain,(
    ! [A_121] :
      ( v1_funct_2('#skF_1',A_121,'#skF_1')
      | A_121 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_377,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_283,c_290,c_42])).

tff(c_378,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_441,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_437,c_378])).

tff(c_429,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_284,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_12])).

tff(c_430,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_463,plain,(
    ! [B_125,C_126] :
      ( k1_relset_1('#skF_1',B_125,C_126) = k1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_430])).

tff(c_465,plain,(
    ! [B_125] : k1_relset_1('#skF_1',B_125,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_429,c_463])).

tff(c_467,plain,(
    ! [B_125] : k1_relset_1('#skF_1',B_125,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_465])).

tff(c_28,plain,(
    ! [C_16,B_15] :
      ( v1_funct_2(C_16,k1_xboole_0,B_15)
      | k1_relset_1(k1_xboole_0,B_15,C_16) != k1_xboole_0
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [C_16,B_15] :
      ( v1_funct_2(C_16,k1_xboole_0,B_15)
      | k1_relset_1(k1_xboole_0,B_15,C_16) != k1_xboole_0
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_504,plain,(
    ! [C_133,B_134] :
      ( v1_funct_2(C_133,'#skF_1',B_134)
      | k1_relset_1('#skF_1',B_134,C_133) != '#skF_1'
      | ~ m1_subset_1(C_133,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_279,c_279,c_44])).

tff(c_506,plain,(
    ! [B_134] :
      ( v1_funct_2('#skF_1','#skF_1',B_134)
      | k1_relset_1('#skF_1',B_134,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_429,c_504])).

tff(c_509,plain,(
    ! [B_134] : v1_funct_2('#skF_1','#skF_1',B_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_506])).

tff(c_442,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_378])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_442])).

tff(c_513,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_543,plain,(
    ! [C_150,A_151,B_152] :
      ( m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ r1_tarski(k2_relat_1(C_150),B_152)
      | ~ r1_tarski(k1_relat_1(C_150),A_151)
      | ~ v1_relat_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_580,plain,(
    ! [C_159,A_160] :
      ( m1_subset_1(C_159,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(C_159),'#skF_1')
      | ~ r1_tarski(k1_relat_1(C_159),A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_543])).

tff(c_582,plain,(
    ! [A_160] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski('#skF_1','#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_160)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_580])).

tff(c_584,plain,(
    ! [A_160] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_582])).

tff(c_599,plain,(
    ! [A_164] : ~ r1_tarski(k1_relat_1('#skF_1'),A_164) ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_584])).

tff(c_604,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.60/1.34  
% 2.60/1.34  %Foreground sorts:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Background operators:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Foreground operators:
% 2.60/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.60/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.34  
% 2.60/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.36  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.60/1.36  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.60/1.36  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.60/1.36  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.60/1.36  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.60/1.36  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.60/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.36  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.36  tff(c_261, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~r1_tarski(k2_relat_1(C_84), B_86) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_157, plain, (![C_45, A_46, B_47]: (m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~r1_tarski(k2_relat_1(C_45), B_47) | ~r1_tarski(k1_relat_1(C_45), A_46) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_20, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.36  tff(c_187, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~r1_tarski(k2_relat_1(C_58), B_57) | ~r1_tarski(k1_relat_1(C_58), A_56) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_157, c_20])).
% 2.60/1.36  tff(c_192, plain, (![A_59, C_60]: (k1_relset_1(A_59, k2_relat_1(C_60), C_60)=k1_relat_1(C_60) | ~r1_tarski(k1_relat_1(C_60), A_59) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.60/1.36  tff(c_196, plain, (![C_60]: (k1_relset_1(k1_relat_1(C_60), k2_relat_1(C_60), C_60)=k1_relat_1(C_60) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_6, c_192])).
% 2.60/1.36  tff(c_77, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.36  tff(c_90, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_40, c_77])).
% 2.60/1.36  tff(c_91, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 2.60/1.36  tff(c_22, plain, (![C_13, A_11, B_12]: (m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~r1_tarski(k2_relat_1(C_13), B_12) | ~r1_tarski(k1_relat_1(C_13), A_11) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_168, plain, (![B_48, C_49, A_50]: (k1_xboole_0=B_48 | v1_funct_2(C_49, A_50, B_48) | k1_relset_1(A_50, B_48, C_49)!=A_50 | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_48))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.36  tff(c_219, plain, (![B_68, C_69, A_70]: (k1_xboole_0=B_68 | v1_funct_2(C_69, A_70, B_68) | k1_relset_1(A_70, B_68, C_69)!=A_70 | ~r1_tarski(k2_relat_1(C_69), B_68) | ~r1_tarski(k1_relat_1(C_69), A_70) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_22, c_168])).
% 2.60/1.36  tff(c_224, plain, (![C_71, A_72]: (k2_relat_1(C_71)=k1_xboole_0 | v1_funct_2(C_71, A_72, k2_relat_1(C_71)) | k1_relset_1(A_72, k2_relat_1(C_71), C_71)!=A_72 | ~r1_tarski(k1_relat_1(C_71), A_72) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_6, c_219])).
% 2.60/1.36  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.36  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.36  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.60/1.36  tff(c_144, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.60/1.36  tff(c_232, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_224, c_144])).
% 2.60/1.36  tff(c_239, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_232])).
% 2.60/1.36  tff(c_240, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_91, c_239])).
% 2.60/1.36  tff(c_243, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_196, c_240])).
% 2.60/1.36  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_243])).
% 2.60/1.36  tff(c_248, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 2.60/1.36  tff(c_267, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_261, c_248])).
% 2.60/1.36  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_6, c_267])).
% 2.60/1.36  tff(c_279, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_90])).
% 2.60/1.36  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.36  tff(c_24, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_14, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.36  tff(c_45, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 2.60/1.36  tff(c_388, plain, (![A_14]: (v1_funct_2('#skF_1', A_14, '#skF_1') | A_14='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_279, c_279, c_279, c_45])).
% 2.60/1.36  tff(c_389, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_388])).
% 2.60/1.36  tff(c_280, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 2.60/1.36  tff(c_290, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_280])).
% 2.60/1.36  tff(c_283, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_10])).
% 2.60/1.36  tff(c_401, plain, (![C_108, A_109, B_110]: (m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~r1_tarski(k2_relat_1(C_108), B_110) | ~r1_tarski(k1_relat_1(C_108), A_109) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_416, plain, (![C_115, A_116]: (m1_subset_1(C_115, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(C_115), '#skF_1') | ~r1_tarski(k1_relat_1(C_115), A_116) | ~v1_relat_1(C_115))), inference(superposition, [status(thm), theory('equality')], [c_283, c_401])).
% 2.60/1.36  tff(c_418, plain, (![A_116]: (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_116) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_290, c_416])).
% 2.60/1.36  tff(c_420, plain, (![A_116]: (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_418])).
% 2.60/1.36  tff(c_422, plain, (![A_117]: (~r1_tarski(k1_relat_1('#skF_1'), A_117))), inference(negUnitSimplification, [status(thm)], [c_389, c_420])).
% 2.60/1.36  tff(c_427, plain, $false, inference(resolution, [status(thm)], [c_6, c_422])).
% 2.60/1.36  tff(c_437, plain, (![A_121]: (v1_funct_2('#skF_1', A_121, '#skF_1') | A_121='#skF_1')), inference(splitRight, [status(thm)], [c_388])).
% 2.60/1.36  tff(c_377, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_283, c_290, c_42])).
% 2.60/1.36  tff(c_378, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_377])).
% 2.60/1.36  tff(c_441, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_437, c_378])).
% 2.60/1.36  tff(c_429, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_388])).
% 2.60/1.36  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.36  tff(c_284, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_12])).
% 2.60/1.36  tff(c_430, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.36  tff(c_463, plain, (![B_125, C_126]: (k1_relset_1('#skF_1', B_125, C_126)=k1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_284, c_430])).
% 2.60/1.36  tff(c_465, plain, (![B_125]: (k1_relset_1('#skF_1', B_125, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_429, c_463])).
% 2.60/1.36  tff(c_467, plain, (![B_125]: (k1_relset_1('#skF_1', B_125, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_465])).
% 2.60/1.36  tff(c_28, plain, (![C_16, B_15]: (v1_funct_2(C_16, k1_xboole_0, B_15) | k1_relset_1(k1_xboole_0, B_15, C_16)!=k1_xboole_0 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.36  tff(c_44, plain, (![C_16, B_15]: (v1_funct_2(C_16, k1_xboole_0, B_15) | k1_relset_1(k1_xboole_0, B_15, C_16)!=k1_xboole_0 | ~m1_subset_1(C_16, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 2.60/1.36  tff(c_504, plain, (![C_133, B_134]: (v1_funct_2(C_133, '#skF_1', B_134) | k1_relset_1('#skF_1', B_134, C_133)!='#skF_1' | ~m1_subset_1(C_133, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_279, c_279, c_44])).
% 2.60/1.36  tff(c_506, plain, (![B_134]: (v1_funct_2('#skF_1', '#skF_1', B_134) | k1_relset_1('#skF_1', B_134, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_429, c_504])).
% 2.60/1.36  tff(c_509, plain, (![B_134]: (v1_funct_2('#skF_1', '#skF_1', B_134))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_506])).
% 2.60/1.36  tff(c_442, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_378])).
% 2.60/1.36  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_509, c_442])).
% 2.60/1.36  tff(c_513, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_377])).
% 2.60/1.36  tff(c_543, plain, (![C_150, A_151, B_152]: (m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~r1_tarski(k2_relat_1(C_150), B_152) | ~r1_tarski(k1_relat_1(C_150), A_151) | ~v1_relat_1(C_150))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_580, plain, (![C_159, A_160]: (m1_subset_1(C_159, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(C_159), '#skF_1') | ~r1_tarski(k1_relat_1(C_159), A_160) | ~v1_relat_1(C_159))), inference(superposition, [status(thm), theory('equality')], [c_283, c_543])).
% 2.60/1.36  tff(c_582, plain, (![A_160]: (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_160) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_290, c_580])).
% 2.60/1.36  tff(c_584, plain, (![A_160]: (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), A_160))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_582])).
% 2.60/1.36  tff(c_599, plain, (![A_164]: (~r1_tarski(k1_relat_1('#skF_1'), A_164))), inference(negUnitSimplification, [status(thm)], [c_513, c_584])).
% 2.60/1.36  tff(c_604, plain, $false, inference(resolution, [status(thm)], [c_6, c_599])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 115
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 7
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 11
% 2.60/1.36  #Demod        : 105
% 2.60/1.36  #Tautology    : 59
% 2.60/1.36  #SimpNegUnit  : 4
% 2.60/1.36  #BackRed      : 6
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.36  Preprocessing        : 0.30
% 2.60/1.36  Parsing              : 0.16
% 2.60/1.36  CNF conversion       : 0.02
% 2.60/1.36  Main loop            : 0.30
% 2.60/1.36  Inferencing          : 0.11
% 2.60/1.36  Reduction            : 0.08
% 2.60/1.36  Demodulation         : 0.06
% 2.60/1.36  BG Simplification    : 0.02
% 2.60/1.36  Subsumption          : 0.06
% 2.60/1.36  Abstraction          : 0.02
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.60/1.36  Total                : 0.63
% 2.60/1.36  Index Insertion      : 0.00
% 2.60/1.36  Index Deletion       : 0.00
% 2.60/1.36  Index Matching       : 0.00
% 2.60/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
