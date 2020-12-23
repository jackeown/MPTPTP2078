%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 277 expanded)
%              Number of leaves         :   42 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 544 expanded)
%              Number of equality atoms :   63 ( 177 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_142,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_150,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_142])).

tff(c_184,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_192,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_184])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_203,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_28])).

tff(c_206,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_203])).

tff(c_218,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(k7_relat_1(B_71,A_72)) = k9_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_230,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_218])).

tff(c_237,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_230])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_314,plain,(
    ! [B_90,A_91,A_92] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_90,A_91),A_92),k9_relat_1(B_90,A_91))
      | ~ v1_relat_1(k7_relat_1(B_90,A_91))
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_24])).

tff(c_323,plain,(
    ! [A_92] :
      ( r1_tarski(k9_relat_1('#skF_4',A_92),k9_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_314])).

tff(c_332,plain,(
    ! [A_92] : r1_tarski(k9_relat_1('#skF_4',A_92),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_150,c_206,c_237,c_323])).

tff(c_34,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_150,c_34])).

tff(c_171,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_298,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_88,k1_tarski(A_89))),k1_tarski(k1_funct_1(B_88,A_89)))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_305,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_298])).

tff(c_311,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_56,c_305])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_339,plain,(
    ! [B_94,C_95,A_96] :
      ( k2_tarski(B_94,C_95) = A_96
      | k1_tarski(C_95) = A_96
      | k1_tarski(B_94) = A_96
      | k1_xboole_0 = A_96
      | ~ r1_tarski(A_96,k2_tarski(B_94,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_351,plain,(
    ! [A_2,A_96] :
      ( k2_tarski(A_2,A_2) = A_96
      | k1_tarski(A_2) = A_96
      | k1_tarski(A_2) = A_96
      | k1_xboole_0 = A_96
      | ~ r1_tarski(A_96,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_339])).

tff(c_366,plain,(
    ! [A_97,A_98] :
      ( k1_tarski(A_97) = A_98
      | k1_tarski(A_97) = A_98
      | k1_tarski(A_97) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k1_tarski(A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_351])).

tff(c_369,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_366])).

tff(c_382,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_369])).

tff(c_270,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k7_relset_1(A_77,B_78,C_79,D_80) = k9_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_276,plain,(
    ! [D_80] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_80) = k9_relat_1('#skF_4',D_80) ),
    inference(resolution,[status(thm)],[c_52,c_270])).

tff(c_48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_288,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_48])).

tff(c_389,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_288])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_389])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_404,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_32])).

tff(c_36,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_159,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_150,c_36])).

tff(c_170,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_396,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_170])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_396])).

tff(c_434,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_441,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_2])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_442,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_434,c_30])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_440,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_20])).

tff(c_514,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_520,plain,(
    ! [A_119] : v4_relat_1('#skF_4',A_119) ),
    inference(resolution,[status(thm)],[c_440,c_514])).

tff(c_523,plain,(
    ! [A_119] :
      ( k7_relat_1('#skF_4',A_119) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_520,c_28])).

tff(c_527,plain,(
    ! [A_120] : k7_relat_1('#skF_4',A_120) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_523])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_532,plain,(
    ! [A_120] :
      ( k9_relat_1('#skF_4',A_120) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_26])).

tff(c_537,plain,(
    ! [A_120] : k9_relat_1('#skF_4',A_120) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_442,c_532])).

tff(c_569,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k7_relset_1(A_129,B_130,C_131,D_132) = k9_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_572,plain,(
    ! [A_129,B_130,D_132] : k7_relset_1(A_129,B_130,'#skF_4',D_132) = k9_relat_1('#skF_4',D_132) ),
    inference(resolution,[status(thm)],[c_440,c_569])).

tff(c_574,plain,(
    ! [A_129,B_130,D_132] : k7_relset_1(A_129,B_130,'#skF_4',D_132) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_572])).

tff(c_575,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_48])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.35  
% 2.61/1.35  %Foreground sorts:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Background operators:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Foreground operators:
% 2.61/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.35  
% 2.79/1.37  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.79/1.37  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.37  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.37  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.37  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.79/1.37  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.79/1.37  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.79/1.37  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.79/1.37  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.79/1.37  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.79/1.37  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.79/1.37  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.79/1.37  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.37  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.37  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.79/1.37  tff(c_142, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.37  tff(c_150, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_142])).
% 2.79/1.37  tff(c_184, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.37  tff(c_192, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_184])).
% 2.79/1.37  tff(c_28, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.79/1.37  tff(c_203, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_28])).
% 2.79/1.37  tff(c_206, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_203])).
% 2.79/1.37  tff(c_218, plain, (![B_71, A_72]: (k2_relat_1(k7_relat_1(B_71, A_72))=k9_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.37  tff(c_230, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_206, c_218])).
% 2.79/1.37  tff(c_237, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_230])).
% 2.79/1.37  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.37  tff(c_314, plain, (![B_90, A_91, A_92]: (r1_tarski(k9_relat_1(k7_relat_1(B_90, A_91), A_92), k9_relat_1(B_90, A_91)) | ~v1_relat_1(k7_relat_1(B_90, A_91)) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_218, c_24])).
% 2.79/1.37  tff(c_323, plain, (![A_92]: (r1_tarski(k9_relat_1('#skF_4', A_92), k9_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_314])).
% 2.79/1.37  tff(c_332, plain, (![A_92]: (r1_tarski(k9_relat_1('#skF_4', A_92), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_150, c_206, c_237, c_323])).
% 2.79/1.37  tff(c_34, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.79/1.37  tff(c_160, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_150, c_34])).
% 2.79/1.37  tff(c_171, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 2.79/1.37  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.79/1.37  tff(c_298, plain, (![B_88, A_89]: (r1_tarski(k2_relat_1(k7_relat_1(B_88, k1_tarski(A_89))), k1_tarski(k1_funct_1(B_88, A_89))) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.79/1.37  tff(c_305, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_206, c_298])).
% 2.79/1.37  tff(c_311, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_56, c_305])).
% 2.79/1.37  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.37  tff(c_339, plain, (![B_94, C_95, A_96]: (k2_tarski(B_94, C_95)=A_96 | k1_tarski(C_95)=A_96 | k1_tarski(B_94)=A_96 | k1_xboole_0=A_96 | ~r1_tarski(A_96, k2_tarski(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.37  tff(c_351, plain, (![A_2, A_96]: (k2_tarski(A_2, A_2)=A_96 | k1_tarski(A_2)=A_96 | k1_tarski(A_2)=A_96 | k1_xboole_0=A_96 | ~r1_tarski(A_96, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_339])).
% 2.79/1.37  tff(c_366, plain, (![A_97, A_98]: (k1_tarski(A_97)=A_98 | k1_tarski(A_97)=A_98 | k1_tarski(A_97)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k1_tarski(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_351])).
% 2.79/1.37  tff(c_369, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_366])).
% 2.79/1.37  tff(c_382, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_171, c_369])).
% 2.79/1.37  tff(c_270, plain, (![A_77, B_78, C_79, D_80]: (k7_relset_1(A_77, B_78, C_79, D_80)=k9_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.37  tff(c_276, plain, (![D_80]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_80)=k9_relat_1('#skF_4', D_80))), inference(resolution, [status(thm)], [c_52, c_270])).
% 2.79/1.37  tff(c_48, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.79/1.37  tff(c_288, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_48])).
% 2.79/1.37  tff(c_389, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_288])).
% 2.79/1.37  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_389])).
% 2.79/1.37  tff(c_394, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_160])).
% 2.79/1.37  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.37  tff(c_404, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_32])).
% 2.79/1.37  tff(c_36, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.79/1.37  tff(c_159, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_150, c_36])).
% 2.79/1.37  tff(c_170, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_159])).
% 2.79/1.37  tff(c_396, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_170])).
% 2.79/1.37  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_396])).
% 2.79/1.37  tff(c_434, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_159])).
% 2.79/1.37  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.37  tff(c_441, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_2])).
% 2.79/1.37  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.37  tff(c_442, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_434, c_30])).
% 2.79/1.37  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.37  tff(c_440, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_20])).
% 2.79/1.37  tff(c_514, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.37  tff(c_520, plain, (![A_119]: (v4_relat_1('#skF_4', A_119))), inference(resolution, [status(thm)], [c_440, c_514])).
% 2.79/1.37  tff(c_523, plain, (![A_119]: (k7_relat_1('#skF_4', A_119)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_520, c_28])).
% 2.79/1.37  tff(c_527, plain, (![A_120]: (k7_relat_1('#skF_4', A_120)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_523])).
% 2.79/1.37  tff(c_26, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.37  tff(c_532, plain, (![A_120]: (k9_relat_1('#skF_4', A_120)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_527, c_26])).
% 2.79/1.37  tff(c_537, plain, (![A_120]: (k9_relat_1('#skF_4', A_120)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_442, c_532])).
% 2.79/1.37  tff(c_569, plain, (![A_129, B_130, C_131, D_132]: (k7_relset_1(A_129, B_130, C_131, D_132)=k9_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.37  tff(c_572, plain, (![A_129, B_130, D_132]: (k7_relset_1(A_129, B_130, '#skF_4', D_132)=k9_relat_1('#skF_4', D_132))), inference(resolution, [status(thm)], [c_440, c_569])).
% 2.79/1.37  tff(c_574, plain, (![A_129, B_130, D_132]: (k7_relset_1(A_129, B_130, '#skF_4', D_132)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_572])).
% 2.79/1.37  tff(c_575, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_48])).
% 2.79/1.37  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_441, c_575])).
% 2.79/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.37  
% 2.79/1.37  Inference rules
% 2.79/1.37  ----------------------
% 2.79/1.37  #Ref     : 0
% 2.79/1.37  #Sup     : 103
% 2.79/1.37  #Fact    : 0
% 2.79/1.37  #Define  : 0
% 2.79/1.37  #Split   : 3
% 2.79/1.37  #Chain   : 0
% 2.79/1.37  #Close   : 0
% 2.79/1.37  
% 2.79/1.37  Ordering : KBO
% 2.79/1.37  
% 2.79/1.37  Simplification rules
% 2.79/1.37  ----------------------
% 2.79/1.37  #Subsume      : 0
% 2.79/1.37  #Demod        : 112
% 2.79/1.37  #Tautology    : 76
% 2.79/1.37  #SimpNegUnit  : 2
% 2.79/1.37  #BackRed      : 25
% 2.79/1.37  
% 2.79/1.37  #Partial instantiations: 0
% 2.79/1.37  #Strategies tried      : 1
% 2.79/1.37  
% 2.79/1.37  Timing (in seconds)
% 2.79/1.37  ----------------------
% 2.79/1.37  Preprocessing        : 0.32
% 2.79/1.37  Parsing              : 0.18
% 2.79/1.37  CNF conversion       : 0.02
% 2.79/1.37  Main loop            : 0.28
% 2.79/1.37  Inferencing          : 0.10
% 2.79/1.37  Reduction            : 0.10
% 2.79/1.38  Demodulation         : 0.07
% 2.79/1.38  BG Simplification    : 0.02
% 2.79/1.38  Subsumption          : 0.04
% 2.79/1.38  Abstraction          : 0.01
% 2.79/1.38  MUC search           : 0.00
% 2.79/1.38  Cooper               : 0.00
% 2.79/1.38  Total                : 0.64
% 2.79/1.38  Index Insertion      : 0.00
% 2.79/1.38  Index Deletion       : 0.00
% 2.79/1.38  Index Matching       : 0.00
% 2.79/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
