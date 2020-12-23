%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 377 expanded)
%              Number of leaves         :   33 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 ( 778 expanded)
%              Number of equality atoms :   48 ( 278 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_91,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_103,c_18])).

tff(c_124,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_224,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_243,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_224])).

tff(c_250,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k2_relset_1(A_81,B_82,C_83),k1_zfmisc_1(B_82))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_250])).

tff(c_289,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_277])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_1'(A_5,B_6),A_5)
      | k1_xboole_0 = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_68)
      | k1_xboole_0 = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_45,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_165,plain,(
    ! [A_67] :
      ( ~ m1_subset_1('#skF_1'(A_67,k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
      | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ m1_subset_1(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_156,c_38])).

tff(c_196,plain,(
    ! [A_67] :
      ( ~ m1_subset_1('#skF_1'(A_67,k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
      | ~ m1_subset_1(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(A_67)) ) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_456,plain,(
    ! [A_95] :
      ( ~ m1_subset_1('#skF_1'(A_95,k2_relat_1('#skF_6')),'#skF_5')
      | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_196])).

tff(c_460,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_456])).

tff(c_463,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_460])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_463])).

tff(c_466,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_499,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_506,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_519,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_506])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_519])).

tff(c_522,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_539,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_14])).

tff(c_660,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_676,plain,(
    ! [A_121,B_122] : k1_relset_1(A_121,B_122,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_539,c_660])).

tff(c_40,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_536,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_40])).

tff(c_703,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_536])).

tff(c_765,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k1_relset_1(A_140,B_141,C_142),k1_zfmisc_1(A_140))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_802,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(A_121))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_765])).

tff(c_820,plain,(
    ! [A_143] : m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(A_143)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_802])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [C_56] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_595,plain,(
    ! [C_56] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_98])).

tff(c_864,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_820,c_595])).

tff(c_533,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_6'
      | A_12 = '#skF_6'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_522,c_18])).

tff(c_872,plain,
    ( k2_relat_1(k1_relat_1('#skF_6')) != '#skF_6'
    | k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_864,c_533])).

tff(c_878,plain,(
    k2_relat_1(k1_relat_1('#skF_6')) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_872])).

tff(c_819,plain,(
    ! [A_121] : m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(A_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_802])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1225,plain,(
    ! [A_168,B_169] : k2_relset_1(A_168,B_169,k1_relat_1('#skF_6')) = k2_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_820,c_30])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k2_relset_1(A_19,B_20,C_21),k1_zfmisc_1(B_20))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1230,plain,(
    ! [B_169,A_168] :
      ( m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')),k1_zfmisc_1(B_169))
      | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_26])).

tff(c_1235,plain,(
    ! [B_169] : m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')),k1_zfmisc_1(B_169)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_1230])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | k1_xboole_0 = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_645,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | B_6 = '#skF_6'
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_10])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_535,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_73])).

tff(c_537,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_522,c_4])).

tff(c_1121,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( r2_hidden('#skF_3'(A_159,B_160,C_161,D_162),C_161)
      | ~ r2_hidden(A_159,D_162)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(B_160,C_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1146,plain,(
    ! [A_159,A_1,D_162] :
      ( r2_hidden('#skF_3'(A_159,A_1,'#skF_6',D_162),'#skF_6')
      | ~ r2_hidden(A_159,D_162)
      | ~ m1_subset_1(D_162,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_1121])).

tff(c_1155,plain,(
    ! [A_163,D_164] :
      ( ~ r2_hidden(A_163,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_1146])).

tff(c_2221,plain,(
    ! [B_260,A_261] :
      ( ~ m1_subset_1(B_260,k1_zfmisc_1('#skF_6'))
      | B_260 = '#skF_6'
      | ~ m1_subset_1(B_260,k1_zfmisc_1(A_261)) ) ),
    inference(resolution,[status(thm)],[c_645,c_1155])).

tff(c_2236,plain,(
    ! [A_261] :
      ( k2_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
      | ~ m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')),k1_zfmisc_1(A_261)) ) ),
    inference(resolution,[status(thm)],[c_1235,c_2221])).

tff(c_2272,plain,(
    k2_relat_1(k1_relat_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_2236])).

tff(c_2274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_2272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:20:10 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.68  
% 3.79/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.69  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.79/1.69  
% 3.79/1.69  %Foreground sorts:
% 3.79/1.69  
% 3.79/1.69  
% 3.79/1.69  %Background operators:
% 3.79/1.69  
% 3.79/1.69  
% 3.79/1.69  %Foreground operators:
% 3.79/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.79/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.79/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.79/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.79/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.79/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.79/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.79/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.79/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.79/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.79/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.79/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.69  
% 3.79/1.70  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.79/1.70  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.79/1.70  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.79/1.70  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.79/1.70  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.79/1.70  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.79/1.70  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.79/1.70  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.79/1.70  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.79/1.70  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.79/1.70  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.79/1.70  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 3.79/1.70  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.79/1.70  tff(c_91, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.79/1.70  tff(c_103, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_91])).
% 3.79/1.70  tff(c_18, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.79/1.70  tff(c_111, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_103, c_18])).
% 3.79/1.70  tff(c_124, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_111])).
% 3.79/1.70  tff(c_224, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.79/1.70  tff(c_243, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_224])).
% 3.79/1.70  tff(c_250, plain, (![A_81, B_82, C_83]: (m1_subset_1(k2_relset_1(A_81, B_82, C_83), k1_zfmisc_1(B_82)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.79/1.70  tff(c_277, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_243, c_250])).
% 3.79/1.70  tff(c_289, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_277])).
% 3.79/1.70  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1('#skF_1'(A_5, B_6), A_5) | k1_xboole_0=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.79/1.70  tff(c_156, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), B_68) | k1_xboole_0=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.79/1.70  tff(c_38, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_45, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.79/1.70  tff(c_165, plain, (![A_67]: (~m1_subset_1('#skF_1'(A_67, k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~m1_subset_1(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_156, c_38])).
% 3.79/1.70  tff(c_196, plain, (![A_67]: (~m1_subset_1('#skF_1'(A_67, k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(A_67)))), inference(splitLeft, [status(thm)], [c_165])).
% 3.79/1.70  tff(c_456, plain, (![A_95]: (~m1_subset_1('#skF_1'(A_95, k2_relat_1('#skF_6')), '#skF_5') | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_196])).
% 3.79/1.70  tff(c_460, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_456])).
% 3.79/1.70  tff(c_463, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_289, c_460])).
% 3.79/1.70  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_463])).
% 3.79/1.70  tff(c_466, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_165])).
% 3.79/1.70  tff(c_499, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.79/1.70  tff(c_506, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_499])).
% 3.79/1.70  tff(c_519, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_466, c_506])).
% 3.79/1.70  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_519])).
% 3.79/1.70  tff(c_522, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_111])).
% 3.79/1.70  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.79/1.70  tff(c_539, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_14])).
% 3.79/1.70  tff(c_660, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.79/1.70  tff(c_676, plain, (![A_121, B_122]: (k1_relset_1(A_121, B_122, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_539, c_660])).
% 3.79/1.70  tff(c_40, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.79/1.70  tff(c_536, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_522, c_40])).
% 3.79/1.70  tff(c_703, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_676, c_536])).
% 3.79/1.70  tff(c_765, plain, (![A_140, B_141, C_142]: (m1_subset_1(k1_relset_1(A_140, B_141, C_142), k1_zfmisc_1(A_140)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.79/1.70  tff(c_802, plain, (![A_121, B_122]: (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(A_121)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(superposition, [status(thm), theory('equality')], [c_676, c_765])).
% 3.79/1.70  tff(c_820, plain, (![A_143]: (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_802])).
% 3.79/1.70  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.70  tff(c_98, plain, (![C_56]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_91])).
% 3.79/1.70  tff(c_595, plain, (![C_56]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_98])).
% 3.79/1.70  tff(c_864, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_820, c_595])).
% 3.79/1.70  tff(c_533, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_6' | A_12='#skF_6' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_522, c_18])).
% 3.79/1.70  tff(c_872, plain, (k2_relat_1(k1_relat_1('#skF_6'))!='#skF_6' | k1_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_864, c_533])).
% 3.79/1.70  tff(c_878, plain, (k2_relat_1(k1_relat_1('#skF_6'))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_703, c_872])).
% 3.79/1.70  tff(c_819, plain, (![A_121]: (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(A_121)))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_802])).
% 3.79/1.70  tff(c_30, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.79/1.70  tff(c_1225, plain, (![A_168, B_169]: (k2_relset_1(A_168, B_169, k1_relat_1('#skF_6'))=k2_relat_1(k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_820, c_30])).
% 3.79/1.70  tff(c_26, plain, (![A_19, B_20, C_21]: (m1_subset_1(k2_relset_1(A_19, B_20, C_21), k1_zfmisc_1(B_20)) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.79/1.70  tff(c_1230, plain, (![B_169, A_168]: (m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')), k1_zfmisc_1(B_169)) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_26])).
% 3.79/1.70  tff(c_1235, plain, (![B_169]: (m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')), k1_zfmisc_1(B_169)))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_1230])).
% 3.79/1.70  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | k1_xboole_0=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.79/1.70  tff(c_645, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | B_6='#skF_6' | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_10])).
% 3.79/1.70  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.70  tff(c_70, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.79/1.70  tff(c_73, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70])).
% 3.79/1.70  tff(c_535, plain, (![A_1]: (~r2_hidden(A_1, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_73])).
% 3.79/1.70  tff(c_537, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_522, c_4])).
% 3.79/1.70  tff(c_1121, plain, (![A_159, B_160, C_161, D_162]: (r2_hidden('#skF_3'(A_159, B_160, C_161, D_162), C_161) | ~r2_hidden(A_159, D_162) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(B_160, C_161))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.79/1.70  tff(c_1146, plain, (![A_159, A_1, D_162]: (r2_hidden('#skF_3'(A_159, A_1, '#skF_6', D_162), '#skF_6') | ~r2_hidden(A_159, D_162) | ~m1_subset_1(D_162, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_537, c_1121])).
% 3.79/1.70  tff(c_1155, plain, (![A_163, D_164]: (~r2_hidden(A_163, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_535, c_1146])).
% 3.79/1.70  tff(c_2221, plain, (![B_260, A_261]: (~m1_subset_1(B_260, k1_zfmisc_1('#skF_6')) | B_260='#skF_6' | ~m1_subset_1(B_260, k1_zfmisc_1(A_261)))), inference(resolution, [status(thm)], [c_645, c_1155])).
% 3.79/1.70  tff(c_2236, plain, (![A_261]: (k2_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~m1_subset_1(k2_relat_1(k1_relat_1('#skF_6')), k1_zfmisc_1(A_261)))), inference(resolution, [status(thm)], [c_1235, c_2221])).
% 3.79/1.70  tff(c_2272, plain, (k2_relat_1(k1_relat_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_2236])).
% 3.79/1.70  tff(c_2274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_2272])).
% 3.79/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.70  
% 3.79/1.70  Inference rules
% 3.79/1.70  ----------------------
% 3.79/1.70  #Ref     : 0
% 3.79/1.70  #Sup     : 485
% 3.79/1.70  #Fact    : 0
% 3.79/1.70  #Define  : 0
% 3.79/1.70  #Split   : 4
% 3.79/1.70  #Chain   : 0
% 3.79/1.70  #Close   : 0
% 3.79/1.70  
% 3.79/1.70  Ordering : KBO
% 3.79/1.70  
% 3.79/1.70  Simplification rules
% 3.79/1.70  ----------------------
% 3.79/1.70  #Subsume      : 31
% 3.79/1.70  #Demod        : 182
% 3.79/1.70  #Tautology    : 126
% 3.79/1.70  #SimpNegUnit  : 19
% 3.79/1.70  #BackRed      : 15
% 3.79/1.70  
% 3.79/1.70  #Partial instantiations: 0
% 3.79/1.70  #Strategies tried      : 1
% 3.79/1.70  
% 3.79/1.70  Timing (in seconds)
% 3.79/1.70  ----------------------
% 3.79/1.71  Preprocessing        : 0.32
% 3.79/1.71  Parsing              : 0.17
% 3.79/1.71  CNF conversion       : 0.02
% 3.79/1.71  Main loop            : 0.59
% 3.79/1.71  Inferencing          : 0.20
% 3.79/1.71  Reduction            : 0.19
% 3.79/1.71  Demodulation         : 0.14
% 3.79/1.71  BG Simplification    : 0.03
% 3.79/1.71  Subsumption          : 0.11
% 3.79/1.71  Abstraction          : 0.04
% 3.79/1.71  MUC search           : 0.00
% 3.79/1.71  Cooper               : 0.00
% 3.79/1.71  Total                : 0.95
% 3.79/1.71  Index Insertion      : 0.00
% 3.79/1.71  Index Deletion       : 0.00
% 3.79/1.71  Index Matching       : 0.00
% 3.79/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
