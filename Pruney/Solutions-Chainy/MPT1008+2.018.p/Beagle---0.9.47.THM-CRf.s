%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 340 expanded)
%              Number of leaves         :   47 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 730 expanded)
%              Number of equality atoms :  122 ( 336 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
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

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_153,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_88,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_178,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_186,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_178])).

tff(c_92,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_194,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_186,c_52])).

tff(c_210,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_448,plain,(
    ! [B_143,A_144] :
      ( k1_tarski(k1_funct_1(B_143,A_144)) = k2_relat_1(B_143)
      | k1_tarski(A_144) != k1_relat_1(B_143)
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_402,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_410,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_402])).

tff(c_84,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_420,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_84])).

tff(c_457,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_420])).

tff(c_479,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_92,c_457])).

tff(c_304,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_312,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_304])).

tff(c_44,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1024,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k1_enumset1(A_237,B_238,C_239) = D_240
      | k2_tarski(A_237,C_239) = D_240
      | k2_tarski(B_238,C_239) = D_240
      | k2_tarski(A_237,B_238) = D_240
      | k1_tarski(C_239) = D_240
      | k1_tarski(B_238) = D_240
      | k1_tarski(A_237) = D_240
      | k1_xboole_0 = D_240
      | ~ r1_tarski(D_240,k1_enumset1(A_237,B_238,C_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1054,plain,(
    ! [A_9,B_10,D_240] :
      ( k1_enumset1(A_9,A_9,B_10) = D_240
      | k2_tarski(A_9,B_10) = D_240
      | k2_tarski(A_9,B_10) = D_240
      | k2_tarski(A_9,A_9) = D_240
      | k1_tarski(B_10) = D_240
      | k1_tarski(A_9) = D_240
      | k1_tarski(A_9) = D_240
      | k1_xboole_0 = D_240
      | ~ r1_tarski(D_240,k2_tarski(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1024])).

tff(c_2389,plain,(
    ! [A_536,B_537,D_538] :
      ( k2_tarski(A_536,B_537) = D_538
      | k2_tarski(A_536,B_537) = D_538
      | k2_tarski(A_536,B_537) = D_538
      | k1_tarski(A_536) = D_538
      | k1_tarski(B_537) = D_538
      | k1_tarski(A_536) = D_538
      | k1_tarski(A_536) = D_538
      | k1_xboole_0 = D_538
      | ~ r1_tarski(D_538,k2_tarski(A_536,B_537)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_1054])).

tff(c_2422,plain,(
    ! [A_8,D_538] :
      ( k2_tarski(A_8,A_8) = D_538
      | k2_tarski(A_8,A_8) = D_538
      | k2_tarski(A_8,A_8) = D_538
      | k1_tarski(A_8) = D_538
      | k1_tarski(A_8) = D_538
      | k1_tarski(A_8) = D_538
      | k1_tarski(A_8) = D_538
      | k1_xboole_0 = D_538
      | ~ r1_tarski(D_538,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2389])).

tff(c_4119,plain,(
    ! [A_868,D_869] :
      ( k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_tarski(A_868) = D_869
      | k1_xboole_0 = D_869
      | ~ r1_tarski(D_869,k1_tarski(A_868)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_14,c_2422])).

tff(c_4149,plain,(
    ! [A_870,B_871] :
      ( k1_tarski(A_870) = k1_relat_1(B_871)
      | k1_relat_1(B_871) = k1_xboole_0
      | ~ v4_relat_1(B_871,k1_tarski(A_870))
      | ~ v1_relat_1(B_871) ) ),
    inference(resolution,[status(thm)],[c_44,c_4119])).

tff(c_4155,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_312,c_4149])).

tff(c_4162,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_4155])).

tff(c_4164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_479,c_4162])).

tff(c_4165,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_4166,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_4184,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_4166])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4175,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_4165,c_46])).

tff(c_4439,plain,(
    ! [B_929,A_930] :
      ( k1_tarski(k1_funct_1(B_929,A_930)) = k2_relat_1(B_929)
      | k1_tarski(A_930) != k1_relat_1(B_929)
      | ~ v1_funct_1(B_929)
      | ~ v1_relat_1(B_929) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4174,plain,(
    ! [A_18] : m1_subset_1('#skF_6',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_38])).

tff(c_4401,plain,(
    ! [A_919,B_920,C_921] :
      ( k2_relset_1(A_919,B_920,C_921) = k2_relat_1(C_921)
      | ~ m1_subset_1(C_921,k1_zfmisc_1(k2_zfmisc_1(A_919,B_920))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4405,plain,(
    ! [A_919,B_920] : k2_relset_1(A_919,B_920,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4174,c_4401])).

tff(c_4407,plain,(
    ! [A_919,B_920] : k2_relset_1(A_919,B_920,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4175,c_4405])).

tff(c_4408,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4407,c_84])).

tff(c_4448,plain,
    ( k2_relat_1('#skF_6') != '#skF_6'
    | k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4439,c_4408])).

tff(c_4469,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_92,c_4184,c_4175,c_4448])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4177,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_86])).

tff(c_90,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_82,plain,(
    ! [B_52,A_51,C_53] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_51,B_52,C_53) = A_51
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_5137,plain,(
    ! [B_1062,A_1063,C_1064] :
      ( B_1062 = '#skF_6'
      | k1_relset_1(A_1063,B_1062,C_1064) = A_1063
      | ~ v1_funct_2(C_1064,A_1063,B_1062)
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(k2_zfmisc_1(A_1063,B_1062))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_82])).

tff(c_5148,plain,(
    ! [B_1065,A_1066] :
      ( B_1065 = '#skF_6'
      | k1_relset_1(A_1066,B_1065,'#skF_6') = A_1066
      | ~ v1_funct_2('#skF_6',A_1066,B_1065) ) ),
    inference(resolution,[status(thm)],[c_4174,c_5137])).

tff(c_5160,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_5148])).

tff(c_5167,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4177,c_5160])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4310,plain,(
    ! [C_902,A_903,B_904] :
      ( v4_relat_1(C_902,A_903)
      | ~ m1_subset_1(C_902,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4315,plain,(
    ! [A_903] : v4_relat_1('#skF_6',A_903) ),
    inference(resolution,[status(thm)],[c_4174,c_4310])).

tff(c_4334,plain,(
    ! [B_909,A_910] :
      ( r1_tarski(k1_relat_1(B_909),A_910)
      | ~ v4_relat_1(B_909,A_910)
      | ~ v1_relat_1(B_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4346,plain,(
    ! [A_910] :
      ( r1_tarski('#skF_6',A_910)
      | ~ v4_relat_1('#skF_6',A_910)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4184,c_4334])).

tff(c_4351,plain,(
    ! [A_910] : r1_tarski('#skF_6',A_910) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_4315,c_4346])).

tff(c_5221,plain,(
    ! [D_1077,A_1078,B_1079,C_1080] :
      ( r2_hidden(k4_tarski(D_1077,'#skF_3'(A_1078,B_1079,C_1080,D_1077)),C_1080)
      | ~ r2_hidden(D_1077,B_1079)
      | k1_relset_1(B_1079,A_1078,C_1080) != B_1079
      | ~ m1_subset_1(C_1080,k1_zfmisc_1(k2_zfmisc_1(B_1079,A_1078))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6021,plain,(
    ! [C_1234,D_1235,A_1236,B_1237] :
      ( ~ r1_tarski(C_1234,k4_tarski(D_1235,'#skF_3'(A_1236,B_1237,C_1234,D_1235)))
      | ~ r2_hidden(D_1235,B_1237)
      | k1_relset_1(B_1237,A_1236,C_1234) != B_1237
      | ~ m1_subset_1(C_1234,k1_zfmisc_1(k2_zfmisc_1(B_1237,A_1236))) ) ),
    inference(resolution,[status(thm)],[c_5221,c_56])).

tff(c_6029,plain,(
    ! [D_1235,B_1237,A_1236] :
      ( ~ r2_hidden(D_1235,B_1237)
      | k1_relset_1(B_1237,A_1236,'#skF_6') != B_1237
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_1237,A_1236))) ) ),
    inference(resolution,[status(thm)],[c_4351,c_6021])).

tff(c_6039,plain,(
    ! [D_1238,B_1239,A_1240] :
      ( ~ r2_hidden(D_1238,B_1239)
      | k1_relset_1(B_1239,A_1240,'#skF_6') != B_1239 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_6029])).

tff(c_6076,plain,(
    ! [A_1241,A_1242,B_1243] :
      ( k1_relset_1(A_1241,A_1242,'#skF_6') != A_1241
      | r1_tarski(A_1241,B_1243) ) ),
    inference(resolution,[status(thm)],[c_6,c_6039])).

tff(c_6087,plain,(
    ! [B_1244] : r1_tarski(k1_tarski('#skF_4'),B_1244) ),
    inference(superposition,[status(thm),theory(equality)],[c_5167,c_6076])).

tff(c_4355,plain,(
    ! [A_911] : r1_tarski('#skF_6',A_911) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_4315,c_4346])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4364,plain,(
    ! [A_911] :
      ( A_911 = '#skF_6'
      | ~ r1_tarski(A_911,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4355,c_8])).

tff(c_6133,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6087,c_4364])).

tff(c_6159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4469,c_6133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.76/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/2.61  
% 7.76/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/2.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.76/2.62  
% 7.76/2.62  %Foreground sorts:
% 7.76/2.62  
% 7.76/2.62  
% 7.76/2.62  %Background operators:
% 7.76/2.62  
% 7.76/2.62  
% 7.76/2.62  %Foreground operators:
% 7.76/2.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.76/2.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.76/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.76/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.76/2.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.76/2.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.76/2.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.76/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.76/2.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.76/2.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.76/2.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.76/2.62  tff('#skF_5', type, '#skF_5': $i).
% 7.76/2.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.76/2.62  tff('#skF_6', type, '#skF_6': $i).
% 7.76/2.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.76/2.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.76/2.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.76/2.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.76/2.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.76/2.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.76/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.76/2.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.76/2.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.76/2.62  tff('#skF_4', type, '#skF_4': $i).
% 7.76/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.76/2.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.76/2.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.76/2.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.76/2.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.76/2.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.76/2.62  
% 7.76/2.63  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 7.76/2.63  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.76/2.63  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.76/2.63  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 7.76/2.63  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.76/2.64  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.76/2.64  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.76/2.64  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.76/2.64  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.76/2.64  tff(f_71, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 7.76/2.64  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.76/2.64  tff(f_73, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.76/2.64  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.76/2.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.76/2.64  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 7.76/2.64  tff(f_109, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.76/2.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.76/2.64  tff(c_88, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.76/2.64  tff(c_178, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.76/2.64  tff(c_186, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_178])).
% 7.76/2.64  tff(c_92, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.76/2.64  tff(c_52, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.76/2.64  tff(c_194, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_186, c_52])).
% 7.76/2.64  tff(c_210, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_194])).
% 7.76/2.64  tff(c_448, plain, (![B_143, A_144]: (k1_tarski(k1_funct_1(B_143, A_144))=k2_relat_1(B_143) | k1_tarski(A_144)!=k1_relat_1(B_143) | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.76/2.64  tff(c_402, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.76/2.64  tff(c_410, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_402])).
% 7.76/2.64  tff(c_84, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.76/2.64  tff(c_420, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_84])).
% 7.76/2.64  tff(c_457, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_448, c_420])).
% 7.76/2.64  tff(c_479, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_92, c_457])).
% 7.76/2.64  tff(c_304, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.64  tff(c_312, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_304])).
% 7.76/2.64  tff(c_44, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.76/2.64  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.76/2.64  tff(c_16, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.76/2.64  tff(c_1024, plain, (![A_237, B_238, C_239, D_240]: (k1_enumset1(A_237, B_238, C_239)=D_240 | k2_tarski(A_237, C_239)=D_240 | k2_tarski(B_238, C_239)=D_240 | k2_tarski(A_237, B_238)=D_240 | k1_tarski(C_239)=D_240 | k1_tarski(B_238)=D_240 | k1_tarski(A_237)=D_240 | k1_xboole_0=D_240 | ~r1_tarski(D_240, k1_enumset1(A_237, B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.76/2.64  tff(c_1054, plain, (![A_9, B_10, D_240]: (k1_enumset1(A_9, A_9, B_10)=D_240 | k2_tarski(A_9, B_10)=D_240 | k2_tarski(A_9, B_10)=D_240 | k2_tarski(A_9, A_9)=D_240 | k1_tarski(B_10)=D_240 | k1_tarski(A_9)=D_240 | k1_tarski(A_9)=D_240 | k1_xboole_0=D_240 | ~r1_tarski(D_240, k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1024])).
% 7.76/2.64  tff(c_2389, plain, (![A_536, B_537, D_538]: (k2_tarski(A_536, B_537)=D_538 | k2_tarski(A_536, B_537)=D_538 | k2_tarski(A_536, B_537)=D_538 | k1_tarski(A_536)=D_538 | k1_tarski(B_537)=D_538 | k1_tarski(A_536)=D_538 | k1_tarski(A_536)=D_538 | k1_xboole_0=D_538 | ~r1_tarski(D_538, k2_tarski(A_536, B_537)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_1054])).
% 7.76/2.64  tff(c_2422, plain, (![A_8, D_538]: (k2_tarski(A_8, A_8)=D_538 | k2_tarski(A_8, A_8)=D_538 | k2_tarski(A_8, A_8)=D_538 | k1_tarski(A_8)=D_538 | k1_tarski(A_8)=D_538 | k1_tarski(A_8)=D_538 | k1_tarski(A_8)=D_538 | k1_xboole_0=D_538 | ~r1_tarski(D_538, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2389])).
% 7.76/2.64  tff(c_4119, plain, (![A_868, D_869]: (k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_tarski(A_868)=D_869 | k1_xboole_0=D_869 | ~r1_tarski(D_869, k1_tarski(A_868)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_14, c_2422])).
% 7.76/2.64  tff(c_4149, plain, (![A_870, B_871]: (k1_tarski(A_870)=k1_relat_1(B_871) | k1_relat_1(B_871)=k1_xboole_0 | ~v4_relat_1(B_871, k1_tarski(A_870)) | ~v1_relat_1(B_871))), inference(resolution, [status(thm)], [c_44, c_4119])).
% 7.76/2.64  tff(c_4155, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_312, c_4149])).
% 7.76/2.64  tff(c_4162, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_186, c_4155])).
% 7.76/2.64  tff(c_4164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_479, c_4162])).
% 7.76/2.64  tff(c_4165, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_194])).
% 7.76/2.64  tff(c_4166, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 7.76/2.64  tff(c_4184, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_4166])).
% 7.76/2.64  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.76/2.64  tff(c_4175, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_4165, c_46])).
% 7.76/2.64  tff(c_4439, plain, (![B_929, A_930]: (k1_tarski(k1_funct_1(B_929, A_930))=k2_relat_1(B_929) | k1_tarski(A_930)!=k1_relat_1(B_929) | ~v1_funct_1(B_929) | ~v1_relat_1(B_929))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.76/2.64  tff(c_38, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.76/2.64  tff(c_4174, plain, (![A_18]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_38])).
% 7.76/2.64  tff(c_4401, plain, (![A_919, B_920, C_921]: (k2_relset_1(A_919, B_920, C_921)=k2_relat_1(C_921) | ~m1_subset_1(C_921, k1_zfmisc_1(k2_zfmisc_1(A_919, B_920))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.76/2.64  tff(c_4405, plain, (![A_919, B_920]: (k2_relset_1(A_919, B_920, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4174, c_4401])).
% 7.76/2.64  tff(c_4407, plain, (![A_919, B_920]: (k2_relset_1(A_919, B_920, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4175, c_4405])).
% 7.76/2.64  tff(c_4408, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4407, c_84])).
% 7.76/2.64  tff(c_4448, plain, (k2_relat_1('#skF_6')!='#skF_6' | k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4439, c_4408])).
% 7.76/2.64  tff(c_4469, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_92, c_4184, c_4175, c_4448])).
% 7.76/2.64  tff(c_86, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.76/2.64  tff(c_4177, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_86])).
% 7.76/2.64  tff(c_90, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.76/2.64  tff(c_82, plain, (![B_52, A_51, C_53]: (k1_xboole_0=B_52 | k1_relset_1(A_51, B_52, C_53)=A_51 | ~v1_funct_2(C_53, A_51, B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.76/2.64  tff(c_5137, plain, (![B_1062, A_1063, C_1064]: (B_1062='#skF_6' | k1_relset_1(A_1063, B_1062, C_1064)=A_1063 | ~v1_funct_2(C_1064, A_1063, B_1062) | ~m1_subset_1(C_1064, k1_zfmisc_1(k2_zfmisc_1(A_1063, B_1062))))), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_82])).
% 7.76/2.64  tff(c_5148, plain, (![B_1065, A_1066]: (B_1065='#skF_6' | k1_relset_1(A_1066, B_1065, '#skF_6')=A_1066 | ~v1_funct_2('#skF_6', A_1066, B_1065))), inference(resolution, [status(thm)], [c_4174, c_5137])).
% 7.76/2.64  tff(c_5160, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_90, c_5148])).
% 7.76/2.64  tff(c_5167, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4177, c_5160])).
% 7.76/2.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.76/2.64  tff(c_4310, plain, (![C_902, A_903, B_904]: (v4_relat_1(C_902, A_903) | ~m1_subset_1(C_902, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.64  tff(c_4315, plain, (![A_903]: (v4_relat_1('#skF_6', A_903))), inference(resolution, [status(thm)], [c_4174, c_4310])).
% 7.76/2.64  tff(c_4334, plain, (![B_909, A_910]: (r1_tarski(k1_relat_1(B_909), A_910) | ~v4_relat_1(B_909, A_910) | ~v1_relat_1(B_909))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.76/2.64  tff(c_4346, plain, (![A_910]: (r1_tarski('#skF_6', A_910) | ~v4_relat_1('#skF_6', A_910) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4184, c_4334])).
% 7.76/2.64  tff(c_4351, plain, (![A_910]: (r1_tarski('#skF_6', A_910))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_4315, c_4346])).
% 7.76/2.64  tff(c_5221, plain, (![D_1077, A_1078, B_1079, C_1080]: (r2_hidden(k4_tarski(D_1077, '#skF_3'(A_1078, B_1079, C_1080, D_1077)), C_1080) | ~r2_hidden(D_1077, B_1079) | k1_relset_1(B_1079, A_1078, C_1080)!=B_1079 | ~m1_subset_1(C_1080, k1_zfmisc_1(k2_zfmisc_1(B_1079, A_1078))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.76/2.64  tff(c_56, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.76/2.64  tff(c_6021, plain, (![C_1234, D_1235, A_1236, B_1237]: (~r1_tarski(C_1234, k4_tarski(D_1235, '#skF_3'(A_1236, B_1237, C_1234, D_1235))) | ~r2_hidden(D_1235, B_1237) | k1_relset_1(B_1237, A_1236, C_1234)!=B_1237 | ~m1_subset_1(C_1234, k1_zfmisc_1(k2_zfmisc_1(B_1237, A_1236))))), inference(resolution, [status(thm)], [c_5221, c_56])).
% 7.76/2.64  tff(c_6029, plain, (![D_1235, B_1237, A_1236]: (~r2_hidden(D_1235, B_1237) | k1_relset_1(B_1237, A_1236, '#skF_6')!=B_1237 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_1237, A_1236))))), inference(resolution, [status(thm)], [c_4351, c_6021])).
% 7.76/2.64  tff(c_6039, plain, (![D_1238, B_1239, A_1240]: (~r2_hidden(D_1238, B_1239) | k1_relset_1(B_1239, A_1240, '#skF_6')!=B_1239)), inference(demodulation, [status(thm), theory('equality')], [c_4174, c_6029])).
% 7.76/2.64  tff(c_6076, plain, (![A_1241, A_1242, B_1243]: (k1_relset_1(A_1241, A_1242, '#skF_6')!=A_1241 | r1_tarski(A_1241, B_1243))), inference(resolution, [status(thm)], [c_6, c_6039])).
% 7.76/2.64  tff(c_6087, plain, (![B_1244]: (r1_tarski(k1_tarski('#skF_4'), B_1244))), inference(superposition, [status(thm), theory('equality')], [c_5167, c_6076])).
% 7.76/2.64  tff(c_4355, plain, (![A_911]: (r1_tarski('#skF_6', A_911))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_4315, c_4346])).
% 7.76/2.64  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.76/2.64  tff(c_4364, plain, (![A_911]: (A_911='#skF_6' | ~r1_tarski(A_911, '#skF_6'))), inference(resolution, [status(thm)], [c_4355, c_8])).
% 7.76/2.64  tff(c_6133, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_6087, c_4364])).
% 7.76/2.64  tff(c_6159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4469, c_6133])).
% 7.76/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/2.64  
% 7.76/2.64  Inference rules
% 7.76/2.64  ----------------------
% 7.76/2.64  #Ref     : 0
% 7.76/2.64  #Sup     : 1470
% 7.76/2.64  #Fact    : 0
% 7.76/2.64  #Define  : 0
% 7.76/2.64  #Split   : 3
% 7.76/2.64  #Chain   : 0
% 7.76/2.64  #Close   : 0
% 7.76/2.64  
% 7.76/2.64  Ordering : KBO
% 7.76/2.64  
% 7.76/2.64  Simplification rules
% 7.76/2.64  ----------------------
% 7.76/2.64  #Subsume      : 342
% 7.76/2.64  #Demod        : 538
% 7.76/2.64  #Tautology    : 281
% 7.76/2.64  #SimpNegUnit  : 6
% 7.76/2.64  #BackRed      : 16
% 7.76/2.64  
% 7.76/2.64  #Partial instantiations: 0
% 7.76/2.64  #Strategies tried      : 1
% 7.76/2.64  
% 7.76/2.64  Timing (in seconds)
% 7.76/2.64  ----------------------
% 7.76/2.64  Preprocessing        : 0.35
% 7.76/2.64  Parsing              : 0.18
% 7.76/2.64  CNF conversion       : 0.02
% 7.76/2.64  Main loop            : 1.54
% 7.76/2.64  Inferencing          : 0.48
% 7.76/2.64  Reduction            : 0.41
% 7.76/2.64  Demodulation         : 0.28
% 7.76/2.64  BG Simplification    : 0.05
% 7.76/2.64  Subsumption          : 0.49
% 7.76/2.64  Abstraction          : 0.06
% 7.76/2.64  MUC search           : 0.00
% 7.76/2.64  Cooper               : 0.00
% 7.76/2.64  Total                : 1.93
% 7.76/2.64  Index Insertion      : 0.00
% 7.76/2.64  Index Deletion       : 0.00
% 7.76/2.64  Index Matching       : 0.00
% 7.76/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
