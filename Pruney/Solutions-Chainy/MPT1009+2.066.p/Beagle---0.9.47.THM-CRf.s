%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 257 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 541 expanded)
%              Number of equality atoms :   93 ( 211 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
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

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_156,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_164,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_174,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_46])).

tff(c_176,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_408,plain,(
    ! [B_117,A_118] :
      ( k1_tarski(k1_funct_1(B_117,A_118)) = k2_relat_1(B_117)
      | k1_tarski(A_118) != k1_relat_1(B_117)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_414,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_58])).

tff(c_441,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_66,c_414])).

tff(c_479,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_239,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_247,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_561,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k1_enumset1(A_153,B_154,C_155) = D_156
      | k2_tarski(A_153,C_155) = D_156
      | k2_tarski(B_154,C_155) = D_156
      | k2_tarski(A_153,B_154) = D_156
      | k1_tarski(C_155) = D_156
      | k1_tarski(B_154) = D_156
      | k1_tarski(A_153) = D_156
      | k1_xboole_0 = D_156
      | ~ r1_tarski(D_156,k1_enumset1(A_153,B_154,C_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_612,plain,(
    ! [A_6,B_7,D_156] :
      ( k1_enumset1(A_6,A_6,B_7) = D_156
      | k2_tarski(A_6,B_7) = D_156
      | k2_tarski(A_6,B_7) = D_156
      | k2_tarski(A_6,A_6) = D_156
      | k1_tarski(B_7) = D_156
      | k1_tarski(A_6) = D_156
      | k1_tarski(A_6) = D_156
      | k1_xboole_0 = D_156
      | ~ r1_tarski(D_156,k2_tarski(A_6,B_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_561])).

tff(c_1363,plain,(
    ! [A_297,B_298,D_299] :
      ( k2_tarski(A_297,B_298) = D_299
      | k2_tarski(A_297,B_298) = D_299
      | k2_tarski(A_297,B_298) = D_299
      | k1_tarski(A_297) = D_299
      | k1_tarski(B_298) = D_299
      | k1_tarski(A_297) = D_299
      | k1_tarski(A_297) = D_299
      | k1_xboole_0 = D_299
      | ~ r1_tarski(D_299,k2_tarski(A_297,B_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_612])).

tff(c_1393,plain,(
    ! [A_5,D_299] :
      ( k2_tarski(A_5,A_5) = D_299
      | k2_tarski(A_5,A_5) = D_299
      | k2_tarski(A_5,A_5) = D_299
      | k1_tarski(A_5) = D_299
      | k1_tarski(A_5) = D_299
      | k1_tarski(A_5) = D_299
      | k1_tarski(A_5) = D_299
      | k1_xboole_0 = D_299
      | ~ r1_tarski(D_299,k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1363])).

tff(c_3675,plain,(
    ! [A_792,D_793] :
      ( k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_tarski(A_792) = D_793
      | k1_xboole_0 = D_793
      | ~ r1_tarski(D_793,k1_tarski(A_792)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_1393])).

tff(c_4073,plain,(
    ! [A_807,B_808] :
      ( k1_tarski(A_807) = k1_relat_1(B_808)
      | k1_relat_1(B_808) = k1_xboole_0
      | ~ v4_relat_1(B_808,k1_tarski(A_807))
      | ~ v1_relat_1(B_808) ) ),
    inference(resolution,[status(thm)],[c_36,c_3675])).

tff(c_4082,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_247,c_4073])).

tff(c_4090,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_4082])).

tff(c_4092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_479,c_4090])).

tff(c_4094,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_4095,plain,(
    ! [A_809,B_810,C_811,D_812] :
      ( k7_relset_1(A_809,B_810,C_811,D_812) = k9_relat_1(C_811,D_812)
      | ~ m1_subset_1(C_811,k1_zfmisc_1(k2_zfmisc_1(A_809,B_810))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4101,plain,(
    ! [D_812] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_812) = k9_relat_1('#skF_4',D_812) ),
    inference(resolution,[status(thm)],[c_62,c_4095])).

tff(c_4300,plain,(
    ! [D_812] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_812) = k9_relat_1('#skF_4',D_812) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4094,c_4101])).

tff(c_4093,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_4374,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4300,c_4094,c_4093])).

tff(c_4377,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4374])).

tff(c_4381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_4377])).

tff(c_4382,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4391,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4382,c_4382,c_40])).

tff(c_44,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_173,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_44])).

tff(c_175,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_4384,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4382,c_175])).

tff(c_4416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4391,c_4384])).

tff(c_4417,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_121,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k9_relat_1(B_57,A_58),k2_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    ! [A_58] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_58),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_125,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_30,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_126,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_133])).

tff(c_139,plain,(
    ! [A_58] : r1_tarski(k9_relat_1(k1_xboole_0,A_58),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_4419,plain,(
    ! [A_58] : r1_tarski(k9_relat_1('#skF_4',A_58),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4417,c_4417,c_139])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4424,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4417,c_4])).

tff(c_4554,plain,(
    ! [A_870,C_871,B_872] :
      ( r1_tarski(A_870,C_871)
      | ~ r1_tarski(B_872,C_871)
      | ~ r1_tarski(A_870,B_872) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4600,plain,(
    ! [A_873,A_874] :
      ( r1_tarski(A_873,A_874)
      | ~ r1_tarski(A_873,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4424,c_4554])).

tff(c_4610,plain,(
    ! [A_58,A_874] : r1_tarski(k9_relat_1('#skF_4',A_58),A_874) ),
    inference(resolution,[status(thm)],[c_4419,c_4600])).

tff(c_4423,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4417,c_30])).

tff(c_4720,plain,(
    ! [A_900,B_901,C_902,D_903] :
      ( k7_relset_1(A_900,B_901,C_902,D_903) = k9_relat_1(C_902,D_903)
      | ~ m1_subset_1(C_902,k1_zfmisc_1(k2_zfmisc_1(A_900,B_901))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4724,plain,(
    ! [A_900,B_901,D_903] : k7_relset_1(A_900,B_901,'#skF_4',D_903) = k9_relat_1('#skF_4',D_903) ),
    inference(resolution,[status(thm)],[c_4423,c_4720])).

tff(c_4725,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4724,c_58])).

tff(c_4728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_4725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:37:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.49  
% 7.02/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.02/2.50  
% 7.02/2.50  %Foreground sorts:
% 7.02/2.50  
% 7.02/2.50  
% 7.02/2.50  %Background operators:
% 7.02/2.50  
% 7.02/2.50  
% 7.02/2.50  %Foreground operators:
% 7.02/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.02/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.02/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.02/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.02/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.02/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.02/2.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.02/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.02/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.02/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.02/2.50  tff('#skF_2', type, '#skF_2': $i).
% 7.02/2.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.02/2.50  tff('#skF_3', type, '#skF_3': $i).
% 7.02/2.50  tff('#skF_1', type, '#skF_1': $i).
% 7.02/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.02/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.02/2.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.02/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.02/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.02/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.02/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.02/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.02/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.02/2.50  
% 7.02/2.51  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 7.02/2.51  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.02/2.51  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 7.02/2.51  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.02/2.51  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 7.02/2.51  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.02/2.51  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.02/2.51  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.02/2.51  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.02/2.51  tff(f_66, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 7.02/2.51  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.02/2.51  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.02/2.51  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.02/2.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.02/2.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.02/2.51  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.02/2.51  tff(c_156, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.02/2.51  tff(c_164, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_156])).
% 7.02/2.51  tff(c_38, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.02/2.51  tff(c_46, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.02/2.51  tff(c_174, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_164, c_46])).
% 7.02/2.51  tff(c_176, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_174])).
% 7.02/2.51  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.02/2.51  tff(c_408, plain, (![B_117, A_118]: (k1_tarski(k1_funct_1(B_117, A_118))=k2_relat_1(B_117) | k1_tarski(A_118)!=k1_relat_1(B_117) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.02/2.51  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.02/2.51  tff(c_414, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_408, c_58])).
% 7.02/2.51  tff(c_441, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_66, c_414])).
% 7.02/2.51  tff(c_479, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_441])).
% 7.02/2.51  tff(c_239, plain, (![C_87, A_88, B_89]: (v4_relat_1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.02/2.51  tff(c_247, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_239])).
% 7.02/2.51  tff(c_36, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.02/2.51  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.02/2.51  tff(c_8, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.02/2.51  tff(c_561, plain, (![A_153, B_154, C_155, D_156]: (k1_enumset1(A_153, B_154, C_155)=D_156 | k2_tarski(A_153, C_155)=D_156 | k2_tarski(B_154, C_155)=D_156 | k2_tarski(A_153, B_154)=D_156 | k1_tarski(C_155)=D_156 | k1_tarski(B_154)=D_156 | k1_tarski(A_153)=D_156 | k1_xboole_0=D_156 | ~r1_tarski(D_156, k1_enumset1(A_153, B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.02/2.51  tff(c_612, plain, (![A_6, B_7, D_156]: (k1_enumset1(A_6, A_6, B_7)=D_156 | k2_tarski(A_6, B_7)=D_156 | k2_tarski(A_6, B_7)=D_156 | k2_tarski(A_6, A_6)=D_156 | k1_tarski(B_7)=D_156 | k1_tarski(A_6)=D_156 | k1_tarski(A_6)=D_156 | k1_xboole_0=D_156 | ~r1_tarski(D_156, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_561])).
% 7.02/2.51  tff(c_1363, plain, (![A_297, B_298, D_299]: (k2_tarski(A_297, B_298)=D_299 | k2_tarski(A_297, B_298)=D_299 | k2_tarski(A_297, B_298)=D_299 | k1_tarski(A_297)=D_299 | k1_tarski(B_298)=D_299 | k1_tarski(A_297)=D_299 | k1_tarski(A_297)=D_299 | k1_xboole_0=D_299 | ~r1_tarski(D_299, k2_tarski(A_297, B_298)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_612])).
% 7.02/2.51  tff(c_1393, plain, (![A_5, D_299]: (k2_tarski(A_5, A_5)=D_299 | k2_tarski(A_5, A_5)=D_299 | k2_tarski(A_5, A_5)=D_299 | k1_tarski(A_5)=D_299 | k1_tarski(A_5)=D_299 | k1_tarski(A_5)=D_299 | k1_tarski(A_5)=D_299 | k1_xboole_0=D_299 | ~r1_tarski(D_299, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1363])).
% 7.02/2.51  tff(c_3675, plain, (![A_792, D_793]: (k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_tarski(A_792)=D_793 | k1_xboole_0=D_793 | ~r1_tarski(D_793, k1_tarski(A_792)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_6, c_1393])).
% 7.02/2.51  tff(c_4073, plain, (![A_807, B_808]: (k1_tarski(A_807)=k1_relat_1(B_808) | k1_relat_1(B_808)=k1_xboole_0 | ~v4_relat_1(B_808, k1_tarski(A_807)) | ~v1_relat_1(B_808))), inference(resolution, [status(thm)], [c_36, c_3675])).
% 7.02/2.51  tff(c_4082, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_247, c_4073])).
% 7.02/2.51  tff(c_4090, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_4082])).
% 7.02/2.51  tff(c_4092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_479, c_4090])).
% 7.02/2.51  tff(c_4094, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_441])).
% 7.02/2.51  tff(c_4095, plain, (![A_809, B_810, C_811, D_812]: (k7_relset_1(A_809, B_810, C_811, D_812)=k9_relat_1(C_811, D_812) | ~m1_subset_1(C_811, k1_zfmisc_1(k2_zfmisc_1(A_809, B_810))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.02/2.51  tff(c_4101, plain, (![D_812]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_812)=k9_relat_1('#skF_4', D_812))), inference(resolution, [status(thm)], [c_62, c_4095])).
% 7.02/2.51  tff(c_4300, plain, (![D_812]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_812)=k9_relat_1('#skF_4', D_812))), inference(demodulation, [status(thm), theory('equality')], [c_4094, c_4101])).
% 7.02/2.51  tff(c_4093, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_441])).
% 7.02/2.51  tff(c_4374, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4300, c_4094, c_4093])).
% 7.02/2.51  tff(c_4377, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4374])).
% 7.02/2.51  tff(c_4381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_4377])).
% 7.02/2.51  tff(c_4382, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_174])).
% 7.02/2.51  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.02/2.51  tff(c_4391, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4382, c_4382, c_40])).
% 7.02/2.51  tff(c_44, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.02/2.51  tff(c_173, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_164, c_44])).
% 7.02/2.51  tff(c_175, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_173])).
% 7.02/2.51  tff(c_4384, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4382, c_175])).
% 7.02/2.51  tff(c_4416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4391, c_4384])).
% 7.02/2.51  tff(c_4417, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_173])).
% 7.02/2.51  tff(c_121, plain, (![B_57, A_58]: (r1_tarski(k9_relat_1(B_57, A_58), k2_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.02/2.51  tff(c_124, plain, (![A_58]: (r1_tarski(k9_relat_1(k1_xboole_0, A_58), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_121])).
% 7.02/2.51  tff(c_125, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_124])).
% 7.02/2.51  tff(c_30, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.02/2.51  tff(c_126, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.02/2.51  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_126])).
% 7.02/2.51  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_133])).
% 7.02/2.51  tff(c_139, plain, (![A_58]: (r1_tarski(k9_relat_1(k1_xboole_0, A_58), k1_xboole_0))), inference(splitRight, [status(thm)], [c_124])).
% 7.02/2.51  tff(c_4419, plain, (![A_58]: (r1_tarski(k9_relat_1('#skF_4', A_58), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4417, c_4417, c_139])).
% 7.02/2.51  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.02/2.51  tff(c_4424, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_4417, c_4])).
% 7.02/2.51  tff(c_4554, plain, (![A_870, C_871, B_872]: (r1_tarski(A_870, C_871) | ~r1_tarski(B_872, C_871) | ~r1_tarski(A_870, B_872))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.02/2.51  tff(c_4600, plain, (![A_873, A_874]: (r1_tarski(A_873, A_874) | ~r1_tarski(A_873, '#skF_4'))), inference(resolution, [status(thm)], [c_4424, c_4554])).
% 7.02/2.51  tff(c_4610, plain, (![A_58, A_874]: (r1_tarski(k9_relat_1('#skF_4', A_58), A_874))), inference(resolution, [status(thm)], [c_4419, c_4600])).
% 7.02/2.51  tff(c_4423, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_4417, c_30])).
% 7.02/2.51  tff(c_4720, plain, (![A_900, B_901, C_902, D_903]: (k7_relset_1(A_900, B_901, C_902, D_903)=k9_relat_1(C_902, D_903) | ~m1_subset_1(C_902, k1_zfmisc_1(k2_zfmisc_1(A_900, B_901))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.02/2.51  tff(c_4724, plain, (![A_900, B_901, D_903]: (k7_relset_1(A_900, B_901, '#skF_4', D_903)=k9_relat_1('#skF_4', D_903))), inference(resolution, [status(thm)], [c_4423, c_4720])).
% 7.02/2.51  tff(c_4725, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4724, c_58])).
% 7.02/2.51  tff(c_4728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4610, c_4725])).
% 7.02/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.51  
% 7.02/2.51  Inference rules
% 7.02/2.51  ----------------------
% 7.02/2.51  #Ref     : 0
% 7.02/2.51  #Sup     : 1279
% 7.02/2.51  #Fact    : 1
% 7.02/2.51  #Define  : 0
% 7.02/2.51  #Split   : 7
% 7.02/2.51  #Chain   : 0
% 7.02/2.51  #Close   : 0
% 7.02/2.51  
% 7.02/2.51  Ordering : KBO
% 7.02/2.51  
% 7.02/2.51  Simplification rules
% 7.02/2.51  ----------------------
% 7.02/2.51  #Subsume      : 269
% 7.02/2.51  #Demod        : 465
% 7.02/2.51  #Tautology    : 263
% 7.02/2.51  #SimpNegUnit  : 7
% 7.02/2.51  #BackRed      : 30
% 7.46/2.51  
% 7.46/2.51  #Partial instantiations: 0
% 7.46/2.51  #Strategies tried      : 1
% 7.46/2.51  
% 7.46/2.51  Timing (in seconds)
% 7.46/2.51  ----------------------
% 7.46/2.52  Preprocessing        : 0.32
% 7.46/2.52  Parsing              : 0.17
% 7.46/2.52  CNF conversion       : 0.02
% 7.46/2.52  Main loop            : 1.37
% 7.46/2.52  Inferencing          : 0.42
% 7.46/2.52  Reduction            : 0.38
% 7.46/2.52  Demodulation         : 0.27
% 7.46/2.52  BG Simplification    : 0.04
% 7.46/2.52  Subsumption          : 0.44
% 7.46/2.52  Abstraction          : 0.05
% 7.46/2.52  MUC search           : 0.00
% 7.46/2.52  Cooper               : 0.00
% 7.46/2.52  Total                : 1.72
% 7.46/2.52  Index Insertion      : 0.00
% 7.46/2.52  Index Deletion       : 0.00
% 7.46/2.52  Index Matching       : 0.00
% 7.46/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
