%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 228 expanded)
%              Number of leaves         :   51 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  198 ( 508 expanded)
%              Number of equality atoms :   45 (  99 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_140,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_152,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_72,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_80,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_78,plain,(
    v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_173,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_185,plain,(
    v4_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_76,c_173])).

tff(c_118,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_130,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_118])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(B_31),A_30)
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_18] : m1_subset_1('#skF_2'(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_tarski(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_609,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_616,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_609])).

tff(c_628,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_616])).

tff(c_629,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_628])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_279,plain,(
    ! [C_124,A_125,B_126] :
      ( r2_hidden(C_124,A_125)
      | ~ r2_hidden(C_124,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_877,plain,(
    ! [A_219,B_220,A_221] :
      ( r2_hidden('#skF_1'(A_219,B_220),A_221)
      | ~ m1_subset_1(A_219,k1_zfmisc_1(A_221))
      | r1_tarski(A_219,B_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_279])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_905,plain,(
    ! [A_222,A_223] :
      ( ~ m1_subset_1(A_222,k1_zfmisc_1(A_223))
      | r1_tarski(A_222,A_223) ) ),
    inference(resolution,[status(thm)],[c_877,c_4])).

tff(c_916,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_905])).

tff(c_334,plain,(
    ! [A_141] :
      ( k1_xboole_0 = A_141
      | r2_hidden(k4_tarski('#skF_3'(A_141),'#skF_4'(A_141)),A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2008,plain,(
    ! [A_287,B_288] :
      ( r2_hidden(k4_tarski('#skF_3'(A_287),'#skF_4'(A_287)),B_288)
      | ~ r1_tarski(A_287,B_288)
      | k1_xboole_0 = A_287
      | ~ v1_relat_1(A_287) ) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15,D_17] :
      ( C_16 = A_14
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(k1_tarski(C_16),D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3322,plain,(
    ! [C_369,A_370,D_371] :
      ( C_369 = '#skF_3'(A_370)
      | ~ r1_tarski(A_370,k2_zfmisc_1(k1_tarski(C_369),D_371))
      | k1_xboole_0 = A_370
      | ~ v1_relat_1(A_370) ) ),
    inference(resolution,[status(thm)],[c_2008,c_22])).

tff(c_3357,plain,
    ( '#skF_3'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_916,c_3322])).

tff(c_3392,plain,
    ( '#skF_3'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_3357])).

tff(c_3404,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3392])).

tff(c_28,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3504,plain,(
    ! [A_24] : m1_subset_1('#skF_9',k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3404,c_28])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3505,plain,(
    ! [A_6] : r1_tarski('#skF_9',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3404,c_8])).

tff(c_975,plain,(
    ! [D_226,A_227,B_228,C_229] :
      ( r2_hidden(k4_tarski(D_226,'#skF_6'(A_227,B_228,C_229,D_226)),C_229)
      | ~ r2_hidden(D_226,B_228)
      | k1_relset_1(B_228,A_227,C_229) != B_228
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(B_228,A_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    ! [B_39,A_38] :
      ( ~ r1_tarski(B_39,A_38)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5483,plain,(
    ! [C_485,D_486,A_487,B_488] :
      ( ~ r1_tarski(C_485,k4_tarski(D_486,'#skF_6'(A_487,B_488,C_485,D_486)))
      | ~ r2_hidden(D_486,B_488)
      | k1_relset_1(B_488,A_487,C_485) != B_488
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(B_488,A_487))) ) ),
    inference(resolution,[status(thm)],[c_975,c_44])).

tff(c_5523,plain,(
    ! [D_486,B_488,A_487] :
      ( ~ r2_hidden(D_486,B_488)
      | k1_relset_1(B_488,A_487,'#skF_9') != B_488
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(B_488,A_487))) ) ),
    inference(resolution,[status(thm)],[c_3505,c_5483])).

tff(c_5541,plain,(
    ! [D_489,B_490,A_491] :
      ( ~ r2_hidden(D_489,B_490)
      | k1_relset_1(B_490,A_491,'#skF_9') != B_490 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3504,c_5523])).

tff(c_5587,plain,(
    ! [A_492,A_493,B_494] :
      ( k1_relset_1(A_492,A_493,'#skF_9') != A_492
      | r1_tarski(A_492,B_494) ) ),
    inference(resolution,[status(thm)],[c_6,c_5541])).

tff(c_5603,plain,(
    ! [B_495] : r1_tarski(k1_tarski('#skF_7'),B_495) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_5587])).

tff(c_134,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,(
    ! [B_85,A_84] :
      ( ~ r1_tarski(B_85,A_84)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_134,c_44])).

tff(c_5655,plain,(
    ! [B_495] :
      ( v1_xboole_0(k1_tarski('#skF_7'))
      | ~ m1_subset_1(B_495,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_5603,c_146])).

tff(c_5682,plain,(
    ! [B_496] : ~ m1_subset_1(B_496,k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_5655])).

tff(c_5698,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_5682])).

tff(c_5700,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3392])).

tff(c_5699,plain,(
    '#skF_3'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3392])).

tff(c_42,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | r2_hidden(k4_tarski('#skF_3'(A_35),'#skF_4'(A_35)),A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_367,plain,(
    ! [A_142,C_143,B_144] :
      ( r2_hidden(A_142,k1_relat_1(C_143))
      | ~ r2_hidden(k4_tarski(A_142,B_144),C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_381,plain,(
    ! [A_145] :
      ( r2_hidden('#skF_3'(A_145),k1_relat_1(A_145))
      | k1_xboole_0 = A_145
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_42,c_367])).

tff(c_390,plain,(
    ! [A_145,B_2] :
      ( r2_hidden('#skF_3'(A_145),B_2)
      | ~ r1_tarski(k1_relat_1(A_145),B_2)
      | k1_xboole_0 = A_145
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_5715,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_2)
      | k1_xboole_0 = '#skF_9'
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_390])).

tff(c_5749,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_2)
      | k1_xboole_0 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_5715])).

tff(c_5883,plain,(
    ! [B_500] :
      ( r2_hidden('#skF_7',B_500)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5700,c_5749])).

tff(c_5891,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_7',A_30)
      | ~ v4_relat_1('#skF_9',A_30)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_5883])).

tff(c_5904,plain,(
    ! [A_501] :
      ( r2_hidden('#skF_7',A_501)
      | ~ v4_relat_1('#skF_9',A_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_5891])).

tff(c_5915,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_185,c_5904])).

tff(c_70,plain,(
    ! [D_65,C_64,B_63,A_62] :
      ( r2_hidden(k1_funct_1(D_65,C_64),B_63)
      | k1_xboole_0 = B_63
      | ~ r2_hidden(C_64,A_62)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(D_65,A_62,B_63)
      | ~ v1_funct_1(D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6161,plain,(
    ! [D_517,B_518] :
      ( r2_hidden(k1_funct_1(D_517,'#skF_7'),B_518)
      | k1_xboole_0 = B_518
      | ~ m1_subset_1(D_517,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),B_518)))
      | ~ v1_funct_2(D_517,k1_tarski('#skF_7'),B_518)
      | ~ v1_funct_1(D_517) ) ),
    inference(resolution,[status(thm)],[c_5915,c_70])).

tff(c_6172,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),'#skF_8')
    | k1_xboole_0 = '#skF_8'
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_6161])).

tff(c_6185,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),'#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_6172])).

tff(c_6187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_6185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.42  
% 6.93/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 6.93/2.42  
% 6.93/2.42  %Foreground sorts:
% 6.93/2.42  
% 6.93/2.42  
% 6.93/2.42  %Background operators:
% 6.93/2.42  
% 6.93/2.42  
% 6.93/2.42  %Foreground operators:
% 6.93/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.93/2.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.93/2.42  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.93/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.93/2.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.93/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.42  tff('#skF_7', type, '#skF_7': $i).
% 6.93/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.93/2.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.93/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.93/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.93/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.93/2.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.93/2.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.93/2.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.93/2.42  tff('#skF_9', type, '#skF_9': $i).
% 6.93/2.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.93/2.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.93/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.93/2.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.93/2.42  tff('#skF_8', type, '#skF_8': $i).
% 6.93/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.93/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.93/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.93/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.93/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.93/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.93/2.42  
% 6.93/2.44  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 6.93/2.44  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.93/2.44  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.93/2.44  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.93/2.44  tff(f_52, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.93/2.44  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.93/2.44  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.93/2.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.93/2.44  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.93/2.44  tff(f_95, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 6.93/2.44  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 6.93/2.44  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.93/2.44  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.93/2.44  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 6.93/2.44  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.93/2.44  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.93/2.44  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 6.93/2.44  tff(f_152, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.93/2.44  tff(c_74, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.44  tff(c_72, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.44  tff(c_80, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.44  tff(c_78, plain, (v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.44  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.44  tff(c_173, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.93/2.44  tff(c_185, plain, (v4_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_173])).
% 6.93/2.44  tff(c_118, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.93/2.44  tff(c_130, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_118])).
% 6.93/2.44  tff(c_36, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(B_31), A_30) | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.93/2.44  tff(c_24, plain, (![A_18]: (m1_subset_1('#skF_2'(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.93/2.44  tff(c_16, plain, (![A_13]: (~v1_xboole_0(k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.44  tff(c_609, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.93/2.44  tff(c_616, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_76, c_609])).
% 6.93/2.44  tff(c_628, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_616])).
% 6.93/2.44  tff(c_629, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_628])).
% 6.93/2.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.93/2.44  tff(c_279, plain, (![C_124, A_125, B_126]: (r2_hidden(C_124, A_125) | ~r2_hidden(C_124, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.93/2.44  tff(c_877, plain, (![A_219, B_220, A_221]: (r2_hidden('#skF_1'(A_219, B_220), A_221) | ~m1_subset_1(A_219, k1_zfmisc_1(A_221)) | r1_tarski(A_219, B_220))), inference(resolution, [status(thm)], [c_6, c_279])).
% 6.93/2.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.93/2.44  tff(c_905, plain, (![A_222, A_223]: (~m1_subset_1(A_222, k1_zfmisc_1(A_223)) | r1_tarski(A_222, A_223))), inference(resolution, [status(thm)], [c_877, c_4])).
% 6.93/2.44  tff(c_916, plain, (r1_tarski('#skF_9', k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_905])).
% 6.93/2.44  tff(c_334, plain, (![A_141]: (k1_xboole_0=A_141 | r2_hidden(k4_tarski('#skF_3'(A_141), '#skF_4'(A_141)), A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.93/2.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.93/2.44  tff(c_2008, plain, (![A_287, B_288]: (r2_hidden(k4_tarski('#skF_3'(A_287), '#skF_4'(A_287)), B_288) | ~r1_tarski(A_287, B_288) | k1_xboole_0=A_287 | ~v1_relat_1(A_287))), inference(resolution, [status(thm)], [c_334, c_2])).
% 6.93/2.44  tff(c_22, plain, (![C_16, A_14, B_15, D_17]: (C_16=A_14 | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(k1_tarski(C_16), D_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.93/2.44  tff(c_3322, plain, (![C_369, A_370, D_371]: (C_369='#skF_3'(A_370) | ~r1_tarski(A_370, k2_zfmisc_1(k1_tarski(C_369), D_371)) | k1_xboole_0=A_370 | ~v1_relat_1(A_370))), inference(resolution, [status(thm)], [c_2008, c_22])).
% 6.93/2.44  tff(c_3357, plain, ('#skF_3'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_916, c_3322])).
% 6.93/2.44  tff(c_3392, plain, ('#skF_3'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_3357])).
% 6.93/2.44  tff(c_3404, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_3392])).
% 6.93/2.44  tff(c_28, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.93/2.44  tff(c_3504, plain, (![A_24]: (m1_subset_1('#skF_9', k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_3404, c_28])).
% 6.93/2.44  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.93/2.44  tff(c_3505, plain, (![A_6]: (r1_tarski('#skF_9', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3404, c_8])).
% 6.93/2.44  tff(c_975, plain, (![D_226, A_227, B_228, C_229]: (r2_hidden(k4_tarski(D_226, '#skF_6'(A_227, B_228, C_229, D_226)), C_229) | ~r2_hidden(D_226, B_228) | k1_relset_1(B_228, A_227, C_229)!=B_228 | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(B_228, A_227))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.44  tff(c_44, plain, (![B_39, A_38]: (~r1_tarski(B_39, A_38) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.93/2.44  tff(c_5483, plain, (![C_485, D_486, A_487, B_488]: (~r1_tarski(C_485, k4_tarski(D_486, '#skF_6'(A_487, B_488, C_485, D_486))) | ~r2_hidden(D_486, B_488) | k1_relset_1(B_488, A_487, C_485)!=B_488 | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(B_488, A_487))))), inference(resolution, [status(thm)], [c_975, c_44])).
% 6.93/2.44  tff(c_5523, plain, (![D_486, B_488, A_487]: (~r2_hidden(D_486, B_488) | k1_relset_1(B_488, A_487, '#skF_9')!=B_488 | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(B_488, A_487))))), inference(resolution, [status(thm)], [c_3505, c_5483])).
% 6.93/2.44  tff(c_5541, plain, (![D_489, B_490, A_491]: (~r2_hidden(D_489, B_490) | k1_relset_1(B_490, A_491, '#skF_9')!=B_490)), inference(demodulation, [status(thm), theory('equality')], [c_3504, c_5523])).
% 6.93/2.44  tff(c_5587, plain, (![A_492, A_493, B_494]: (k1_relset_1(A_492, A_493, '#skF_9')!=A_492 | r1_tarski(A_492, B_494))), inference(resolution, [status(thm)], [c_6, c_5541])).
% 6.93/2.44  tff(c_5603, plain, (![B_495]: (r1_tarski(k1_tarski('#skF_7'), B_495))), inference(superposition, [status(thm), theory('equality')], [c_629, c_5587])).
% 6.93/2.44  tff(c_134, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | v1_xboole_0(B_85) | ~m1_subset_1(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.93/2.44  tff(c_146, plain, (![B_85, A_84]: (~r1_tarski(B_85, A_84) | v1_xboole_0(B_85) | ~m1_subset_1(A_84, B_85))), inference(resolution, [status(thm)], [c_134, c_44])).
% 6.93/2.44  tff(c_5655, plain, (![B_495]: (v1_xboole_0(k1_tarski('#skF_7')) | ~m1_subset_1(B_495, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_5603, c_146])).
% 6.93/2.44  tff(c_5682, plain, (![B_496]: (~m1_subset_1(B_496, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_16, c_5655])).
% 6.93/2.44  tff(c_5698, plain, $false, inference(resolution, [status(thm)], [c_24, c_5682])).
% 6.93/2.44  tff(c_5700, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_3392])).
% 6.93/2.44  tff(c_5699, plain, ('#skF_3'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_3392])).
% 6.93/2.44  tff(c_42, plain, (![A_35]: (k1_xboole_0=A_35 | r2_hidden(k4_tarski('#skF_3'(A_35), '#skF_4'(A_35)), A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.93/2.44  tff(c_367, plain, (![A_142, C_143, B_144]: (r2_hidden(A_142, k1_relat_1(C_143)) | ~r2_hidden(k4_tarski(A_142, B_144), C_143) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.93/2.44  tff(c_381, plain, (![A_145]: (r2_hidden('#skF_3'(A_145), k1_relat_1(A_145)) | k1_xboole_0=A_145 | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_42, c_367])).
% 6.93/2.44  tff(c_390, plain, (![A_145, B_2]: (r2_hidden('#skF_3'(A_145), B_2) | ~r1_tarski(k1_relat_1(A_145), B_2) | k1_xboole_0=A_145 | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_381, c_2])).
% 6.93/2.44  tff(c_5715, plain, (![B_2]: (r2_hidden('#skF_7', B_2) | ~r1_tarski(k1_relat_1('#skF_9'), B_2) | k1_xboole_0='#skF_9' | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5699, c_390])).
% 6.93/2.44  tff(c_5749, plain, (![B_2]: (r2_hidden('#skF_7', B_2) | ~r1_tarski(k1_relat_1('#skF_9'), B_2) | k1_xboole_0='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_5715])).
% 6.93/2.44  tff(c_5883, plain, (![B_500]: (r2_hidden('#skF_7', B_500) | ~r1_tarski(k1_relat_1('#skF_9'), B_500))), inference(negUnitSimplification, [status(thm)], [c_5700, c_5749])).
% 6.93/2.44  tff(c_5891, plain, (![A_30]: (r2_hidden('#skF_7', A_30) | ~v4_relat_1('#skF_9', A_30) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_5883])).
% 6.93/2.44  tff(c_5904, plain, (![A_501]: (r2_hidden('#skF_7', A_501) | ~v4_relat_1('#skF_9', A_501))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_5891])).
% 6.93/2.44  tff(c_5915, plain, (r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_185, c_5904])).
% 6.93/2.44  tff(c_70, plain, (![D_65, C_64, B_63, A_62]: (r2_hidden(k1_funct_1(D_65, C_64), B_63) | k1_xboole_0=B_63 | ~r2_hidden(C_64, A_62) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(D_65, A_62, B_63) | ~v1_funct_1(D_65))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.93/2.44  tff(c_6161, plain, (![D_517, B_518]: (r2_hidden(k1_funct_1(D_517, '#skF_7'), B_518) | k1_xboole_0=B_518 | ~m1_subset_1(D_517, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), B_518))) | ~v1_funct_2(D_517, k1_tarski('#skF_7'), B_518) | ~v1_funct_1(D_517))), inference(resolution, [status(thm)], [c_5915, c_70])).
% 6.93/2.44  tff(c_6172, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), '#skF_8') | k1_xboole_0='#skF_8' | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_6161])).
% 6.93/2.44  tff(c_6185, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), '#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_6172])).
% 6.93/2.44  tff(c_6187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_6185])).
% 6.93/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.44  
% 6.93/2.44  Inference rules
% 6.93/2.44  ----------------------
% 6.93/2.44  #Ref     : 0
% 6.93/2.44  #Sup     : 1259
% 6.93/2.44  #Fact    : 0
% 6.93/2.44  #Define  : 0
% 6.93/2.44  #Split   : 14
% 6.93/2.44  #Chain   : 0
% 6.93/2.44  #Close   : 0
% 6.93/2.44  
% 6.93/2.44  Ordering : KBO
% 6.93/2.44  
% 6.93/2.44  Simplification rules
% 6.93/2.44  ----------------------
% 6.93/2.44  #Subsume      : 134
% 6.93/2.44  #Demod        : 819
% 6.93/2.44  #Tautology    : 536
% 6.93/2.44  #SimpNegUnit  : 17
% 6.93/2.44  #BackRed      : 105
% 6.93/2.44  
% 6.93/2.44  #Partial instantiations: 0
% 6.93/2.44  #Strategies tried      : 1
% 6.93/2.44  
% 6.93/2.44  Timing (in seconds)
% 6.93/2.44  ----------------------
% 6.93/2.44  Preprocessing        : 0.35
% 6.93/2.44  Parsing              : 0.19
% 6.93/2.44  CNF conversion       : 0.02
% 6.93/2.44  Main loop            : 1.30
% 6.93/2.44  Inferencing          : 0.41
% 6.93/2.44  Reduction            : 0.46
% 6.93/2.44  Demodulation         : 0.33
% 6.93/2.44  BG Simplification    : 0.05
% 6.93/2.44  Subsumption          : 0.27
% 6.93/2.44  Abstraction          : 0.05
% 6.93/2.44  MUC search           : 0.00
% 6.93/2.44  Cooper               : 0.00
% 6.93/2.44  Total                : 1.69
% 6.93/2.44  Index Insertion      : 0.00
% 6.93/2.44  Index Deletion       : 0.00
% 6.93/2.44  Index Matching       : 0.00
% 6.93/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
