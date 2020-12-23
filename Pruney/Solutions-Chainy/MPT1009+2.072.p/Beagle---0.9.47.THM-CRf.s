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
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 289 expanded)
%              Number of leaves         :   43 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 588 expanded)
%              Number of equality atoms :   97 ( 219 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_189,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_197,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_189])).

tff(c_252,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_260,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_252])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_271,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_260,c_36])).

tff(c_274,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_271])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_311,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_34])).

tff(c_315,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_311])).

tff(c_220,plain,(
    ! [B_81,A_82] :
      ( k2_relat_1(k7_relat_1(B_81,A_82)) = k9_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_428,plain,(
    ! [B_118,A_119,A_120] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_118,A_119),A_120),k9_relat_1(B_118,A_119))
      | ~ v1_relat_1(k7_relat_1(B_118,A_119))
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_32])).

tff(c_434,plain,(
    ! [A_120] :
      ( r1_tarski(k9_relat_1('#skF_4',A_120),k9_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_428])).

tff(c_444,plain,(
    ! [A_120] : r1_tarski(k9_relat_1('#skF_4',A_120),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_197,c_274,c_315,c_434])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_207,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_197,c_42])).

tff(c_209,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_344,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_109,k1_tarski(A_110))),k1_tarski(k1_funct_1(B_109,A_110)))
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_347,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_344])).

tff(c_357,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_64,c_347])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k1_enumset1(A_112,B_113,C_114) = D_115
      | k2_tarski(A_112,C_114) = D_115
      | k2_tarski(B_113,C_114) = D_115
      | k2_tarski(A_112,B_113) = D_115
      | k1_tarski(C_114) = D_115
      | k1_tarski(B_113) = D_115
      | k1_tarski(A_112) = D_115
      | k1_xboole_0 = D_115
      | ~ r1_tarski(D_115,k1_enumset1(A_112,B_113,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_391,plain,(
    ! [A_3,B_4,D_115] :
      ( k1_enumset1(A_3,A_3,B_4) = D_115
      | k2_tarski(A_3,B_4) = D_115
      | k2_tarski(A_3,B_4) = D_115
      | k2_tarski(A_3,A_3) = D_115
      | k1_tarski(B_4) = D_115
      | k1_tarski(A_3) = D_115
      | k1_tarski(A_3) = D_115
      | k1_xboole_0 = D_115
      | ~ r1_tarski(D_115,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_370])).

tff(c_454,plain,(
    ! [A_122,B_123,D_124] :
      ( k2_tarski(A_122,B_123) = D_124
      | k2_tarski(A_122,B_123) = D_124
      | k2_tarski(A_122,B_123) = D_124
      | k1_tarski(A_122) = D_124
      | k1_tarski(B_123) = D_124
      | k1_tarski(A_122) = D_124
      | k1_tarski(A_122) = D_124
      | k1_xboole_0 = D_124
      | ~ r1_tarski(D_124,k2_tarski(A_122,B_123)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_391])).

tff(c_466,plain,(
    ! [A_2,D_124] :
      ( k2_tarski(A_2,A_2) = D_124
      | k2_tarski(A_2,A_2) = D_124
      | k2_tarski(A_2,A_2) = D_124
      | k1_tarski(A_2) = D_124
      | k1_tarski(A_2) = D_124
      | k1_tarski(A_2) = D_124
      | k1_tarski(A_2) = D_124
      | k1_xboole_0 = D_124
      | ~ r1_tarski(D_124,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_454])).

tff(c_480,plain,(
    ! [A_125,D_126] :
      ( k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_tarski(A_125) = D_126
      | k1_xboole_0 = D_126
      | ~ r1_tarski(D_126,k1_tarski(A_125)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_466])).

tff(c_486,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_357,c_480])).

tff(c_500,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_486])).

tff(c_328,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k7_relset_1(A_102,B_103,C_104,D_105) = k9_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_334,plain,(
    ! [D_105] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_105) = k9_relat_1('#skF_4',D_105) ),
    inference(resolution,[status(thm)],[c_60,c_328])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_360,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_56])).

tff(c_506,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_360])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_506])).

tff(c_511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_521,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_511,c_40])).

tff(c_44,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_206,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_197,c_44])).

tff(c_208,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_513,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_208])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_513])).

tff(c_546,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_553,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_2])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_554,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_546,c_38])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_552,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_28])).

tff(c_629,plain,(
    ! [C_141,A_142,B_143] :
      ( v4_relat_1(C_141,A_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_635,plain,(
    ! [A_144] : v4_relat_1('#skF_4',A_144) ),
    inference(resolution,[status(thm)],[c_552,c_629])).

tff(c_638,plain,(
    ! [A_144] :
      ( k7_relat_1('#skF_4',A_144) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_635,c_36])).

tff(c_642,plain,(
    ! [A_145] : k7_relat_1('#skF_4',A_145) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_638])).

tff(c_647,plain,(
    ! [A_145] :
      ( k9_relat_1('#skF_4',A_145) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_34])).

tff(c_652,plain,(
    ! [A_145] : k9_relat_1('#skF_4',A_145) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_554,c_647])).

tff(c_691,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k7_relset_1(A_158,B_159,C_160,D_161) = k9_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_694,plain,(
    ! [A_158,B_159,D_161] : k7_relset_1(A_158,B_159,'#skF_4',D_161) = k9_relat_1('#skF_4',D_161) ),
    inference(resolution,[status(thm)],[c_552,c_691])).

tff(c_696,plain,(
    ! [A_158,B_159,D_161] : k7_relset_1(A_158,B_159,'#skF_4',D_161) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_694])).

tff(c_697,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_56])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:02:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.41  
% 2.80/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.80/1.41  
% 2.80/1.41  %Foreground sorts:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Background operators:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Foreground operators:
% 2.80/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.80/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.80/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.80/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.41  
% 2.80/1.43  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.80/1.43  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.80/1.43  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.80/1.43  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.80/1.43  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.80/1.43  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.80/1.43  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.80/1.43  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.80/1.43  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.43  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.80/1.43  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 2.80/1.43  tff(f_113, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.80/1.43  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.80/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.43  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.80/1.43  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.80/1.43  tff(c_189, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.80/1.43  tff(c_197, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_189])).
% 2.80/1.43  tff(c_252, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.80/1.43  tff(c_260, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_252])).
% 2.80/1.43  tff(c_36, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.43  tff(c_271, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_260, c_36])).
% 2.80/1.43  tff(c_274, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_271])).
% 2.80/1.43  tff(c_34, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.43  tff(c_311, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_274, c_34])).
% 2.80/1.43  tff(c_315, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_311])).
% 2.80/1.43  tff(c_220, plain, (![B_81, A_82]: (k2_relat_1(k7_relat_1(B_81, A_82))=k9_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.43  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.43  tff(c_428, plain, (![B_118, A_119, A_120]: (r1_tarski(k9_relat_1(k7_relat_1(B_118, A_119), A_120), k9_relat_1(B_118, A_119)) | ~v1_relat_1(k7_relat_1(B_118, A_119)) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_220, c_32])).
% 2.80/1.43  tff(c_434, plain, (![A_120]: (r1_tarski(k9_relat_1('#skF_4', A_120), k9_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_428])).
% 2.80/1.43  tff(c_444, plain, (![A_120]: (r1_tarski(k9_relat_1('#skF_4', A_120), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_197, c_274, c_315, c_434])).
% 2.80/1.43  tff(c_42, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_207, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_197, c_42])).
% 2.80/1.43  tff(c_209, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_207])).
% 2.80/1.43  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.80/1.43  tff(c_344, plain, (![B_109, A_110]: (r1_tarski(k2_relat_1(k7_relat_1(B_109, k1_tarski(A_110))), k1_tarski(k1_funct_1(B_109, A_110))) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_347, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_274, c_344])).
% 2.80/1.43  tff(c_357, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_64, c_347])).
% 2.80/1.43  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.43  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.43  tff(c_370, plain, (![A_112, B_113, C_114, D_115]: (k1_enumset1(A_112, B_113, C_114)=D_115 | k2_tarski(A_112, C_114)=D_115 | k2_tarski(B_113, C_114)=D_115 | k2_tarski(A_112, B_113)=D_115 | k1_tarski(C_114)=D_115 | k1_tarski(B_113)=D_115 | k1_tarski(A_112)=D_115 | k1_xboole_0=D_115 | ~r1_tarski(D_115, k1_enumset1(A_112, B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.80/1.43  tff(c_391, plain, (![A_3, B_4, D_115]: (k1_enumset1(A_3, A_3, B_4)=D_115 | k2_tarski(A_3, B_4)=D_115 | k2_tarski(A_3, B_4)=D_115 | k2_tarski(A_3, A_3)=D_115 | k1_tarski(B_4)=D_115 | k1_tarski(A_3)=D_115 | k1_tarski(A_3)=D_115 | k1_xboole_0=D_115 | ~r1_tarski(D_115, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_370])).
% 2.80/1.43  tff(c_454, plain, (![A_122, B_123, D_124]: (k2_tarski(A_122, B_123)=D_124 | k2_tarski(A_122, B_123)=D_124 | k2_tarski(A_122, B_123)=D_124 | k1_tarski(A_122)=D_124 | k1_tarski(B_123)=D_124 | k1_tarski(A_122)=D_124 | k1_tarski(A_122)=D_124 | k1_xboole_0=D_124 | ~r1_tarski(D_124, k2_tarski(A_122, B_123)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_391])).
% 2.80/1.43  tff(c_466, plain, (![A_2, D_124]: (k2_tarski(A_2, A_2)=D_124 | k2_tarski(A_2, A_2)=D_124 | k2_tarski(A_2, A_2)=D_124 | k1_tarski(A_2)=D_124 | k1_tarski(A_2)=D_124 | k1_tarski(A_2)=D_124 | k1_tarski(A_2)=D_124 | k1_xboole_0=D_124 | ~r1_tarski(D_124, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_454])).
% 2.80/1.43  tff(c_480, plain, (![A_125, D_126]: (k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_tarski(A_125)=D_126 | k1_xboole_0=D_126 | ~r1_tarski(D_126, k1_tarski(A_125)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_466])).
% 2.80/1.43  tff(c_486, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_357, c_480])).
% 2.80/1.43  tff(c_500, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_209, c_486])).
% 2.80/1.43  tff(c_328, plain, (![A_102, B_103, C_104, D_105]: (k7_relset_1(A_102, B_103, C_104, D_105)=k9_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_334, plain, (![D_105]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_105)=k9_relat_1('#skF_4', D_105))), inference(resolution, [status(thm)], [c_60, c_328])).
% 2.80/1.43  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.80/1.43  tff(c_360, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_56])).
% 2.80/1.43  tff(c_506, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_500, c_360])).
% 2.80/1.43  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_444, c_506])).
% 2.80/1.43  tff(c_511, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_207])).
% 2.80/1.43  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.43  tff(c_521, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_511, c_40])).
% 2.80/1.43  tff(c_44, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_206, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_197, c_44])).
% 2.80/1.43  tff(c_208, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_206])).
% 2.80/1.43  tff(c_513, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_208])).
% 2.80/1.43  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_521, c_513])).
% 2.80/1.43  tff(c_546, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_206])).
% 2.80/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.43  tff(c_553, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_2])).
% 2.80/1.43  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.43  tff(c_554, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_546, c_38])).
% 2.80/1.43  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.43  tff(c_552, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_28])).
% 2.80/1.43  tff(c_629, plain, (![C_141, A_142, B_143]: (v4_relat_1(C_141, A_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.80/1.43  tff(c_635, plain, (![A_144]: (v4_relat_1('#skF_4', A_144))), inference(resolution, [status(thm)], [c_552, c_629])).
% 2.80/1.43  tff(c_638, plain, (![A_144]: (k7_relat_1('#skF_4', A_144)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_635, c_36])).
% 2.80/1.43  tff(c_642, plain, (![A_145]: (k7_relat_1('#skF_4', A_145)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_638])).
% 2.80/1.43  tff(c_647, plain, (![A_145]: (k9_relat_1('#skF_4', A_145)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_642, c_34])).
% 2.80/1.43  tff(c_652, plain, (![A_145]: (k9_relat_1('#skF_4', A_145)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_554, c_647])).
% 2.80/1.43  tff(c_691, plain, (![A_158, B_159, C_160, D_161]: (k7_relset_1(A_158, B_159, C_160, D_161)=k9_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_694, plain, (![A_158, B_159, D_161]: (k7_relset_1(A_158, B_159, '#skF_4', D_161)=k9_relat_1('#skF_4', D_161))), inference(resolution, [status(thm)], [c_552, c_691])).
% 2.80/1.43  tff(c_696, plain, (![A_158, B_159, D_161]: (k7_relset_1(A_158, B_159, '#skF_4', D_161)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_694])).
% 2.80/1.43  tff(c_697, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_56])).
% 2.80/1.43  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_553, c_697])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 0
% 2.80/1.43  #Sup     : 128
% 2.80/1.43  #Fact    : 0
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 3
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 0
% 2.80/1.43  #Demod        : 133
% 2.80/1.43  #Tautology    : 97
% 2.80/1.43  #SimpNegUnit  : 2
% 2.80/1.43  #BackRed      : 25
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.44  Preprocessing        : 0.32
% 2.80/1.44  Parsing              : 0.17
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.34
% 2.80/1.44  Inferencing          : 0.12
% 2.80/1.44  Reduction            : 0.12
% 2.80/1.44  Demodulation         : 0.09
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.05
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.69
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
