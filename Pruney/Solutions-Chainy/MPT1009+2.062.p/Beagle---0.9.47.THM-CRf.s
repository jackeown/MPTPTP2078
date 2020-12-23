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
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 333 expanded)
%              Number of leaves         :   44 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 ( 731 expanded)
%              Number of equality atoms :   97 ( 236 expanded)
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

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_132,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_48,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_148,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_48])).

tff(c_164,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_334,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(k1_funct_1(B_105,A_106)) = k2_relat_1(B_105)
      | k1_tarski(A_106) != k1_relat_1(B_105)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_340,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_60])).

tff(c_367,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_68,c_340])).

tff(c_369,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_244,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_252,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_244])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_451,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k1_enumset1(A_123,B_124,C_125) = D_126
      | k2_tarski(A_123,C_125) = D_126
      | k2_tarski(B_124,C_125) = D_126
      | k2_tarski(A_123,B_124) = D_126
      | k1_tarski(C_125) = D_126
      | k1_tarski(B_124) = D_126
      | k1_tarski(A_123) = D_126
      | k1_xboole_0 = D_126
      | ~ r1_tarski(D_126,k1_enumset1(A_123,B_124,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_473,plain,(
    ! [A_3,B_4,D_126] :
      ( k1_enumset1(A_3,A_3,B_4) = D_126
      | k2_tarski(A_3,B_4) = D_126
      | k2_tarski(A_3,B_4) = D_126
      | k2_tarski(A_3,A_3) = D_126
      | k1_tarski(B_4) = D_126
      | k1_tarski(A_3) = D_126
      | k1_tarski(A_3) = D_126
      | k1_xboole_0 = D_126
      | ~ r1_tarski(D_126,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_451])).

tff(c_583,plain,(
    ! [A_147,B_148,D_149] :
      ( k2_tarski(A_147,B_148) = D_149
      | k2_tarski(A_147,B_148) = D_149
      | k2_tarski(A_147,B_148) = D_149
      | k1_tarski(A_147) = D_149
      | k1_tarski(B_148) = D_149
      | k1_tarski(A_147) = D_149
      | k1_tarski(A_147) = D_149
      | k1_xboole_0 = D_149
      | ~ r1_tarski(D_149,k2_tarski(A_147,B_148)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_473])).

tff(c_622,plain,(
    ! [A_150,B_151,B_152] :
      ( k2_tarski(A_150,B_151) = k1_relat_1(B_152)
      | k1_tarski(B_151) = k1_relat_1(B_152)
      | k1_tarski(A_150) = k1_relat_1(B_152)
      | k1_relat_1(B_152) = k1_xboole_0
      | ~ v4_relat_1(B_152,k2_tarski(A_150,B_151))
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_34,c_583])).

tff(c_629,plain,(
    ! [A_2,B_152] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_152)
      | k1_tarski(A_2) = k1_relat_1(B_152)
      | k1_tarski(A_2) = k1_relat_1(B_152)
      | k1_relat_1(B_152) = k1_xboole_0
      | ~ v4_relat_1(B_152,k1_tarski(A_2))
      | ~ v1_relat_1(B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_622])).

tff(c_634,plain,(
    ! [A_153,B_154] :
      ( k1_tarski(A_153) = k1_relat_1(B_154)
      | k1_tarski(A_153) = k1_relat_1(B_154)
      | k1_tarski(A_153) = k1_relat_1(B_154)
      | k1_relat_1(B_154) = k1_xboole_0
      | ~ v4_relat_1(B_154,k1_tarski(A_153))
      | ~ v1_relat_1(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_629])).

tff(c_640,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_252,c_634])).

tff(c_647,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_640])).

tff(c_649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_369,c_647])).

tff(c_651,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_268,plain,(
    ! [B_95,A_96] :
      ( k7_relat_1(B_95,A_96) = B_95
      | ~ v4_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_271,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_252,c_268])).

tff(c_277,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_271])).

tff(c_654,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_277])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_317,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_38])).

tff(c_321,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_317])).

tff(c_652,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_321])).

tff(c_256,plain,(
    ! [B_93,A_94] :
      ( k2_relat_1(k7_relat_1(B_93,A_94)) = k9_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1183,plain,(
    ! [B_199,A_200,A_201] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_199,A_200),A_201),k9_relat_1(B_199,A_200))
      | ~ v1_relat_1(k7_relat_1(B_199,A_200))
      | ~ v1_relat_1(B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_36])).

tff(c_1219,plain,(
    ! [A_201] :
      ( r1_tarski(k9_relat_1('#skF_4',A_201),k9_relat_1('#skF_4',k1_relat_1('#skF_4')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_1183])).

tff(c_1249,plain,(
    ! [A_201] : r1_tarski(k9_relat_1('#skF_4',A_201),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_654,c_652,c_1219])).

tff(c_657,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_64])).

tff(c_58,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k7_relset_1(A_33,B_34,C_35,D_36) = k9_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_764,plain,(
    ! [D_36] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_36) = k9_relat_1('#skF_4',D_36) ),
    inference(resolution,[status(thm)],[c_657,c_58])).

tff(c_650,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_1182,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_650])).

tff(c_1275,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_1182])).

tff(c_1279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1275])).

tff(c_1280,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1288,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_2])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1286,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_1280,c_42])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1285,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_28])).

tff(c_1373,plain,(
    ! [C_221,A_222,B_223] :
      ( v4_relat_1(C_221,A_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1378,plain,(
    ! [A_222] : v4_relat_1('#skF_4',A_222) ),
    inference(resolution,[status(thm)],[c_1285,c_1373])).

tff(c_1393,plain,(
    ! [B_231,A_232] :
      ( k7_relat_1(B_231,A_232) = B_231
      | ~ v4_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1396,plain,(
    ! [A_222] :
      ( k7_relat_1('#skF_4',A_222) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1378,c_1393])).

tff(c_1399,plain,(
    ! [A_222] : k7_relat_1('#skF_4',A_222) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1396])).

tff(c_1426,plain,(
    ! [B_239,A_240] :
      ( k2_relat_1(k7_relat_1(B_239,A_240)) = k9_relat_1(B_239,A_240)
      | ~ v1_relat_1(B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1438,plain,(
    ! [A_222] :
      ( k9_relat_1('#skF_4',A_222) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_1426])).

tff(c_1442,plain,(
    ! [A_222] : k9_relat_1('#skF_4',A_222) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1286,c_1438])).

tff(c_1498,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k7_relset_1(A_249,B_250,C_251,D_252) = k9_relat_1(C_251,D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1501,plain,(
    ! [A_249,B_250,D_252] : k7_relset_1(A_249,B_250,'#skF_4',D_252) = k9_relat_1('#skF_4',D_252) ),
    inference(resolution,[status(thm)],[c_1285,c_1498])).

tff(c_1503,plain,(
    ! [A_249,B_250,D_252] : k7_relset_1(A_249,B_250,'#skF_4',D_252) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1501])).

tff(c_1504,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_60])).

tff(c_1507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.56  
% 3.62/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.62/1.57  
% 3.62/1.57  %Foreground sorts:
% 3.62/1.57  
% 3.62/1.57  
% 3.62/1.57  %Background operators:
% 3.62/1.57  
% 3.62/1.57  
% 3.62/1.57  %Foreground operators:
% 3.62/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.62/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.62/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.62/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.62/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.62/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.62/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.57  
% 3.62/1.59  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.62/1.59  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.62/1.59  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.62/1.59  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.62/1.59  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.62/1.59  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.62/1.59  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.62/1.59  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.62/1.59  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.62/1.59  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.62/1.59  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.62/1.59  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.62/1.59  tff(f_121, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.62/1.59  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.62/1.59  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.62/1.59  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.62/1.59  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.62/1.59  tff(c_132, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.62/1.59  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_132])).
% 3.62/1.59  tff(c_48, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.62/1.59  tff(c_148, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_48])).
% 3.62/1.59  tff(c_164, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_148])).
% 3.62/1.59  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.62/1.59  tff(c_334, plain, (![B_105, A_106]: (k1_tarski(k1_funct_1(B_105, A_106))=k2_relat_1(B_105) | k1_tarski(A_106)!=k1_relat_1(B_105) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.62/1.59  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.62/1.59  tff(c_340, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_334, c_60])).
% 3.62/1.59  tff(c_367, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_68, c_340])).
% 3.62/1.59  tff(c_369, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_367])).
% 3.62/1.59  tff(c_244, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.62/1.59  tff(c_252, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_244])).
% 3.62/1.59  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.59  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.62/1.59  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.59  tff(c_451, plain, (![A_123, B_124, C_125, D_126]: (k1_enumset1(A_123, B_124, C_125)=D_126 | k2_tarski(A_123, C_125)=D_126 | k2_tarski(B_124, C_125)=D_126 | k2_tarski(A_123, B_124)=D_126 | k1_tarski(C_125)=D_126 | k1_tarski(B_124)=D_126 | k1_tarski(A_123)=D_126 | k1_xboole_0=D_126 | ~r1_tarski(D_126, k1_enumset1(A_123, B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.62/1.59  tff(c_473, plain, (![A_3, B_4, D_126]: (k1_enumset1(A_3, A_3, B_4)=D_126 | k2_tarski(A_3, B_4)=D_126 | k2_tarski(A_3, B_4)=D_126 | k2_tarski(A_3, A_3)=D_126 | k1_tarski(B_4)=D_126 | k1_tarski(A_3)=D_126 | k1_tarski(A_3)=D_126 | k1_xboole_0=D_126 | ~r1_tarski(D_126, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_451])).
% 3.62/1.59  tff(c_583, plain, (![A_147, B_148, D_149]: (k2_tarski(A_147, B_148)=D_149 | k2_tarski(A_147, B_148)=D_149 | k2_tarski(A_147, B_148)=D_149 | k1_tarski(A_147)=D_149 | k1_tarski(B_148)=D_149 | k1_tarski(A_147)=D_149 | k1_tarski(A_147)=D_149 | k1_xboole_0=D_149 | ~r1_tarski(D_149, k2_tarski(A_147, B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_473])).
% 3.62/1.59  tff(c_622, plain, (![A_150, B_151, B_152]: (k2_tarski(A_150, B_151)=k1_relat_1(B_152) | k1_tarski(B_151)=k1_relat_1(B_152) | k1_tarski(A_150)=k1_relat_1(B_152) | k1_relat_1(B_152)=k1_xboole_0 | ~v4_relat_1(B_152, k2_tarski(A_150, B_151)) | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_34, c_583])).
% 3.62/1.59  tff(c_629, plain, (![A_2, B_152]: (k2_tarski(A_2, A_2)=k1_relat_1(B_152) | k1_tarski(A_2)=k1_relat_1(B_152) | k1_tarski(A_2)=k1_relat_1(B_152) | k1_relat_1(B_152)=k1_xboole_0 | ~v4_relat_1(B_152, k1_tarski(A_2)) | ~v1_relat_1(B_152))), inference(superposition, [status(thm), theory('equality')], [c_4, c_622])).
% 3.62/1.59  tff(c_634, plain, (![A_153, B_154]: (k1_tarski(A_153)=k1_relat_1(B_154) | k1_tarski(A_153)=k1_relat_1(B_154) | k1_tarski(A_153)=k1_relat_1(B_154) | k1_relat_1(B_154)=k1_xboole_0 | ~v4_relat_1(B_154, k1_tarski(A_153)) | ~v1_relat_1(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_629])).
% 3.62/1.59  tff(c_640, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_252, c_634])).
% 3.62/1.59  tff(c_647, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_640])).
% 3.62/1.59  tff(c_649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_369, c_647])).
% 3.62/1.59  tff(c_651, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_367])).
% 3.62/1.59  tff(c_268, plain, (![B_95, A_96]: (k7_relat_1(B_95, A_96)=B_95 | ~v4_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.59  tff(c_271, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_252, c_268])).
% 3.62/1.59  tff(c_277, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_271])).
% 3.62/1.59  tff(c_654, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_651, c_277])).
% 3.62/1.59  tff(c_38, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.59  tff(c_317, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_277, c_38])).
% 3.62/1.59  tff(c_321, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_317])).
% 3.62/1.59  tff(c_652, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_321])).
% 3.62/1.59  tff(c_256, plain, (![B_93, A_94]: (k2_relat_1(k7_relat_1(B_93, A_94))=k9_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.59  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.62/1.59  tff(c_1183, plain, (![B_199, A_200, A_201]: (r1_tarski(k9_relat_1(k7_relat_1(B_199, A_200), A_201), k9_relat_1(B_199, A_200)) | ~v1_relat_1(k7_relat_1(B_199, A_200)) | ~v1_relat_1(B_199))), inference(superposition, [status(thm), theory('equality')], [c_256, c_36])).
% 3.62/1.59  tff(c_1219, plain, (![A_201]: (r1_tarski(k9_relat_1('#skF_4', A_201), k9_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1(k7_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_654, c_1183])).
% 3.62/1.59  tff(c_1249, plain, (![A_201]: (r1_tarski(k9_relat_1('#skF_4', A_201), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_654, c_652, c_1219])).
% 3.62/1.59  tff(c_657, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_64])).
% 3.62/1.59  tff(c_58, plain, (![A_33, B_34, C_35, D_36]: (k7_relset_1(A_33, B_34, C_35, D_36)=k9_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.62/1.59  tff(c_764, plain, (![D_36]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_36)=k9_relat_1('#skF_4', D_36))), inference(resolution, [status(thm)], [c_657, c_58])).
% 3.62/1.59  tff(c_650, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_367])).
% 3.62/1.59  tff(c_1182, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_650])).
% 3.62/1.59  tff(c_1275, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_1182])).
% 3.62/1.59  tff(c_1279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1275])).
% 3.62/1.59  tff(c_1280, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_148])).
% 3.62/1.59  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.59  tff(c_1288, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_2])).
% 3.62/1.59  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.62/1.59  tff(c_1286, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_1280, c_42])).
% 3.62/1.59  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.59  tff(c_1285, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_28])).
% 3.62/1.59  tff(c_1373, plain, (![C_221, A_222, B_223]: (v4_relat_1(C_221, A_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.62/1.59  tff(c_1378, plain, (![A_222]: (v4_relat_1('#skF_4', A_222))), inference(resolution, [status(thm)], [c_1285, c_1373])).
% 3.62/1.59  tff(c_1393, plain, (![B_231, A_232]: (k7_relat_1(B_231, A_232)=B_231 | ~v4_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.59  tff(c_1396, plain, (![A_222]: (k7_relat_1('#skF_4', A_222)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1378, c_1393])).
% 3.62/1.59  tff(c_1399, plain, (![A_222]: (k7_relat_1('#skF_4', A_222)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1396])).
% 3.62/1.59  tff(c_1426, plain, (![B_239, A_240]: (k2_relat_1(k7_relat_1(B_239, A_240))=k9_relat_1(B_239, A_240) | ~v1_relat_1(B_239))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.59  tff(c_1438, plain, (![A_222]: (k9_relat_1('#skF_4', A_222)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_1426])).
% 3.62/1.59  tff(c_1442, plain, (![A_222]: (k9_relat_1('#skF_4', A_222)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1286, c_1438])).
% 3.62/1.59  tff(c_1498, plain, (![A_249, B_250, C_251, D_252]: (k7_relset_1(A_249, B_250, C_251, D_252)=k9_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.62/1.59  tff(c_1501, plain, (![A_249, B_250, D_252]: (k7_relset_1(A_249, B_250, '#skF_4', D_252)=k9_relat_1('#skF_4', D_252))), inference(resolution, [status(thm)], [c_1285, c_1498])).
% 3.62/1.59  tff(c_1503, plain, (![A_249, B_250, D_252]: (k7_relset_1(A_249, B_250, '#skF_4', D_252)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1501])).
% 3.62/1.59  tff(c_1504, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_60])).
% 3.62/1.59  tff(c_1507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1504])).
% 3.62/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  
% 3.62/1.59  Inference rules
% 3.62/1.59  ----------------------
% 3.62/1.59  #Ref     : 0
% 3.62/1.59  #Sup     : 310
% 3.62/1.59  #Fact    : 0
% 3.62/1.59  #Define  : 0
% 3.62/1.59  #Split   : 5
% 3.62/1.59  #Chain   : 0
% 3.62/1.59  #Close   : 0
% 3.62/1.59  
% 3.62/1.59  Ordering : KBO
% 3.62/1.59  
% 3.62/1.59  Simplification rules
% 3.62/1.59  ----------------------
% 3.62/1.59  #Subsume      : 18
% 3.62/1.59  #Demod        : 303
% 3.62/1.59  #Tautology    : 196
% 3.62/1.59  #SimpNegUnit  : 4
% 3.62/1.59  #BackRed      : 21
% 3.62/1.59  
% 3.62/1.59  #Partial instantiations: 0
% 3.62/1.59  #Strategies tried      : 1
% 3.62/1.59  
% 3.62/1.59  Timing (in seconds)
% 3.62/1.59  ----------------------
% 3.62/1.59  Preprocessing        : 0.33
% 3.62/1.59  Parsing              : 0.18
% 3.62/1.59  CNF conversion       : 0.02
% 3.62/1.59  Main loop            : 0.50
% 3.62/1.59  Inferencing          : 0.18
% 3.62/1.59  Reduction            : 0.18
% 3.62/1.59  Demodulation         : 0.13
% 3.62/1.59  BG Simplification    : 0.02
% 3.62/1.59  Subsumption          : 0.08
% 3.62/1.59  Abstraction          : 0.02
% 3.62/1.59  MUC search           : 0.00
% 3.62/1.59  Cooper               : 0.00
% 3.62/1.59  Total                : 0.87
% 3.62/1.59  Index Insertion      : 0.00
% 3.62/1.59  Index Deletion       : 0.00
% 3.62/1.59  Index Matching       : 0.00
% 3.62/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
