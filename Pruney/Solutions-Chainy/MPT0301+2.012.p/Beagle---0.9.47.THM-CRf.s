%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 946 expanded)
%              Number of leaves         :   30 ( 289 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (1851 expanded)
%              Number of equality atoms :   94 (1015 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_486,plain,(
    ! [B_152,A_153] :
      ( ~ r1_xboole_0(B_152,A_153)
      | ~ r1_tarski(B_152,A_153)
      | v1_xboole_0(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_491,plain,(
    ! [A_154] :
      ( ~ r1_tarski(A_154,k1_xboole_0)
      | v1_xboole_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_10,c_486])).

tff(c_496,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_491])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_72,plain,(
    ! [B_56,A_57] :
      ( ~ r1_xboole_0(B_56,A_57)
      | ~ r1_tarski(B_56,A_57)
      | v1_xboole_0(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    ! [A_58] :
      ( ~ r1_tarski(A_58,k1_xboole_0)
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_87,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_103,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( r2_hidden(k4_tarski(A_71,B_72),k2_zfmisc_1(C_73,D_74))
      | ~ r2_hidden(B_72,D_74)
      | ~ r2_hidden(A_71,C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [C_75,D_76,B_77,A_78] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_75,D_76))
      | ~ r2_hidden(B_77,D_76)
      | ~ r2_hidden(A_78,C_75) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_121,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_77,'#skF_12')
      | ~ r2_hidden(A_78,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_119])).

tff(c_123,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden(B_77,'#skF_12')
      | ~ r2_hidden(A_78,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_121])).

tff(c_135,plain,(
    ! [A_82] : ~ r2_hidden(A_82,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_147,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_147])).

tff(c_156,plain,(
    ! [B_83] : ~ r2_hidden(B_83,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_168])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_181,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6])).

tff(c_18,plain,(
    ! [A_11,B_12,D_38] :
      ( r2_hidden('#skF_8'(A_11,B_12,k2_zfmisc_1(A_11,B_12),D_38),B_12)
      | ~ r2_hidden(D_38,k2_zfmisc_1(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_183,plain,(
    ! [A_7] : r1_tarski('#skF_10',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_8])).

tff(c_76,plain,(
    ! [A_8] :
      ( ~ r1_tarski(A_8,k1_xboole_0)
      | v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_198,plain,(
    ! [A_87] :
      ( ~ r1_tarski(A_87,'#skF_10')
      | v1_xboole_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_76])).

tff(c_203,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_183,c_198])).

tff(c_229,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_hidden('#skF_7'(A_101,B_102,k2_zfmisc_1(A_101,B_102),D_103),A_101)
      | ~ r2_hidden(D_103,k2_zfmisc_1(A_101,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_234,plain,(
    ! [A_104,D_105,B_106] :
      ( ~ v1_xboole_0(A_104)
      | ~ r2_hidden(D_105,k2_zfmisc_1(A_104,B_106)) ) ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_259,plain,(
    ! [A_109,B_110] :
      ( ~ v1_xboole_0(A_109)
      | k2_zfmisc_1(A_109,B_110) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_181,c_234])).

tff(c_276,plain,(
    ! [B_114] : k2_zfmisc_1('#skF_10',B_114) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_203,c_259])).

tff(c_233,plain,(
    ! [A_101,D_103,B_102] :
      ( ~ v1_xboole_0(A_101)
      | ~ r2_hidden(D_103,k2_zfmisc_1(A_101,B_102)) ) ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_287,plain,(
    ! [D_103] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_103,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_233])).

tff(c_310,plain,(
    ! [D_115] : ~ r2_hidden(D_115,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_287])).

tff(c_334,plain,(
    ! [D_116,A_117] : ~ r2_hidden(D_116,k2_zfmisc_1(A_117,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_18,c_310])).

tff(c_361,plain,(
    ! [A_117] : k2_zfmisc_1(A_117,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_181,c_334])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_178,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_71])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_178])).

tff(c_367,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_375,plain,(
    ! [A_7] : r1_tarski('#skF_9',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_8])).

tff(c_390,plain,(
    ! [A_121] :
      ( ~ r1_tarski(A_121,'#skF_9')
      | v1_xboole_0(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_76])).

tff(c_395,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_375,c_390])).

tff(c_373,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_6])).

tff(c_422,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_hidden('#skF_7'(A_139,B_140,k2_zfmisc_1(A_139,B_140),D_141),A_139)
      | ~ r2_hidden(D_141,k2_zfmisc_1(A_139,B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_427,plain,(
    ! [A_142,D_143,B_144] :
      ( ~ v1_xboole_0(A_142)
      | ~ r2_hidden(D_143,k2_zfmisc_1(A_142,B_144)) ) ),
    inference(resolution,[status(thm)],[c_422,c_2])).

tff(c_465,plain,(
    ! [A_150,B_151] :
      ( ~ v1_xboole_0(A_150)
      | k2_zfmisc_1(A_150,B_151) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_373,c_427])).

tff(c_471,plain,(
    ! [B_151] : k2_zfmisc_1('#skF_9',B_151) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_395,c_465])).

tff(c_370,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_71])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_370])).

tff(c_476,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_520,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( r2_hidden(k4_tarski(A_171,B_172),k2_zfmisc_1(C_173,D_174))
      | ~ r2_hidden(B_172,D_174)
      | ~ r2_hidden(A_171,C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_539,plain,(
    ! [C_175,D_176,B_177,A_178] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_175,D_176))
      | ~ r2_hidden(B_177,D_176)
      | ~ r2_hidden(A_178,C_175) ) ),
    inference(resolution,[status(thm)],[c_520,c_2])).

tff(c_541,plain,(
    ! [B_177,A_178] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_177,'#skF_10')
      | ~ r2_hidden(A_178,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_539])).

tff(c_545,plain,(
    ! [B_177,A_178] :
      ( ~ r2_hidden(B_177,'#skF_10')
      | ~ r2_hidden(A_178,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_541])).

tff(c_550,plain,(
    ! [A_179] : ~ r2_hidden(A_179,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_560,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_550])).

tff(c_590,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_70])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_593,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_58])).

tff(c_475,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_543,plain,(
    ! [B_177,A_178] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_177,'#skF_12')
      | ~ r2_hidden(A_178,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_539])).

tff(c_547,plain,(
    ! [B_177,A_178] :
      ( ~ r2_hidden(B_177,'#skF_12')
      | ~ r2_hidden(A_178,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_543])).

tff(c_852,plain,(
    ! [A_201] : ~ r2_hidden(A_201,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_874,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_852])).

tff(c_59,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_2'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_591,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(A_53)
      | A_53 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_63])).

tff(c_879,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_874,c_591])).

tff(c_883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_879])).

tff(c_885,plain,(
    ! [B_202] : ~ r2_hidden(B_202,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_907,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_885])).

tff(c_910,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_907,c_591])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_590,c_910])).

tff(c_917,plain,(
    ! [B_203] : ~ r2_hidden(B_203,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_927,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_917])).

tff(c_958,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_70])).

tff(c_961,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_58])).

tff(c_1218,plain,(
    ! [A_225] : ~ r2_hidden(A_225,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_1238,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1218])).

tff(c_959,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(A_53)
      | A_53 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_63])).

tff(c_1241,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1238,c_959])).

tff(c_1245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_961,c_1241])).

tff(c_1247,plain,(
    ! [B_226] : ~ r2_hidden(B_226,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_1267,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_1247])).

tff(c_1270,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1267,c_959])).

tff(c_1274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_958,c_1270])).

tff(c_1276,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1278,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_6])).

tff(c_1280,plain,(
    ! [A_7] : r1_tarski('#skF_12',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_8])).

tff(c_1281,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_10])).

tff(c_1404,plain,(
    ! [B_265,A_266] :
      ( ~ r1_xboole_0(B_265,A_266)
      | ~ r1_tarski(B_265,A_266)
      | v1_xboole_0(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1409,plain,(
    ! [A_267] :
      ( ~ r1_tarski(A_267,'#skF_12')
      | v1_xboole_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_1281,c_1404])).

tff(c_1414,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_1280,c_1409])).

tff(c_1438,plain,(
    ! [A_284,B_285,D_286] :
      ( r2_hidden('#skF_7'(A_284,B_285,k2_zfmisc_1(A_284,B_285),D_286),A_284)
      | ~ r2_hidden(D_286,k2_zfmisc_1(A_284,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1443,plain,(
    ! [A_287,D_288,B_289] :
      ( ~ v1_xboole_0(A_287)
      | ~ r2_hidden(D_288,k2_zfmisc_1(A_287,B_289)) ) ),
    inference(resolution,[status(thm)],[c_1438,c_2])).

tff(c_1481,plain,(
    ! [A_295,B_296] :
      ( ~ v1_xboole_0(A_295)
      | k2_zfmisc_1(A_295,B_296) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1278,c_1443])).

tff(c_1488,plain,(
    ! [B_297] : k2_zfmisc_1('#skF_12',B_297) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1414,c_1481])).

tff(c_1442,plain,(
    ! [A_284,D_286,B_285] :
      ( ~ v1_xboole_0(A_284)
      | ~ r2_hidden(D_286,k2_zfmisc_1(A_284,B_285)) ) ),
    inference(resolution,[status(thm)],[c_1438,c_2])).

tff(c_1499,plain,(
    ! [D_286] :
      ( ~ v1_xboole_0('#skF_12')
      | ~ r2_hidden(D_286,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_1442])).

tff(c_1545,plain,(
    ! [D_301] : ~ r2_hidden(D_301,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1499])).

tff(c_1576,plain,(
    ! [D_302,A_303] : ~ r2_hidden(D_302,k2_zfmisc_1(A_303,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_18,c_1545])).

tff(c_1613,plain,(
    ! [A_303] : k2_zfmisc_1(A_303,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1278,c_1576])).

tff(c_1304,plain,(
    ! [B_231,A_232] :
      ( ~ r1_xboole_0(B_231,A_232)
      | ~ r1_tarski(B_231,A_232)
      | v1_xboole_0(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1309,plain,(
    ! [A_233] :
      ( ~ r1_tarski(A_233,'#skF_12')
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_1281,c_1304])).

tff(c_1314,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_1280,c_1309])).

tff(c_1337,plain,(
    ! [A_250,B_251,D_252] :
      ( r2_hidden('#skF_7'(A_250,B_251,k2_zfmisc_1(A_250,B_251),D_252),A_250)
      | ~ r2_hidden(D_252,k2_zfmisc_1(A_250,B_251)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1342,plain,(
    ! [A_253,D_254,B_255] :
      ( ~ v1_xboole_0(A_253)
      | ~ r2_hidden(D_254,k2_zfmisc_1(A_253,B_255)) ) ),
    inference(resolution,[status(thm)],[c_1337,c_2])).

tff(c_1380,plain,(
    ! [A_261,B_262] :
      ( ~ v1_xboole_0(A_261)
      | k2_zfmisc_1(A_261,B_262) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1278,c_1342])).

tff(c_1386,plain,(
    ! [B_262] : k2_zfmisc_1('#skF_12',B_262) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1314,c_1380])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1290,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1276,c_1276,c_46])).

tff(c_1291,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1275,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1288,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1275])).

tff(c_1292,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_1288])).

tff(c_1389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1292])).

tff(c_1390,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_1393,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1288])).

tff(c_1618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1393])).

tff(c_1620,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1619,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1629,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1620,c_1619])).

tff(c_1630,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1629])).

tff(c_1633,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1620])).

tff(c_1646,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_6])).

tff(c_1621,plain,(
    ! [A_7] : r1_tarski('#skF_11',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_8])).

tff(c_1632,plain,(
    ! [A_7] : r1_tarski('#skF_10',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1621])).

tff(c_1622,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_10])).

tff(c_1631,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1622])).

tff(c_1661,plain,(
    ! [B_311,A_312] :
      ( ~ r1_xboole_0(B_311,A_312)
      | ~ r1_tarski(B_311,A_312)
      | v1_xboole_0(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1667,plain,(
    ! [A_313] :
      ( ~ r1_tarski(A_313,'#skF_10')
      | v1_xboole_0(A_313) ) ),
    inference(resolution,[status(thm)],[c_1631,c_1661])).

tff(c_1672,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1632,c_1667])).

tff(c_1695,plain,(
    ! [A_330,B_331,D_332] :
      ( r2_hidden('#skF_7'(A_330,B_331,k2_zfmisc_1(A_330,B_331),D_332),A_330)
      | ~ r2_hidden(D_332,k2_zfmisc_1(A_330,B_331)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1700,plain,(
    ! [A_333,D_334,B_335] :
      ( ~ v1_xboole_0(A_333)
      | ~ r2_hidden(D_334,k2_zfmisc_1(A_333,B_335)) ) ),
    inference(resolution,[status(thm)],[c_1695,c_2])).

tff(c_1738,plain,(
    ! [A_341,B_342] :
      ( ~ v1_xboole_0(A_341)
      | k2_zfmisc_1(A_341,B_342) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1646,c_1700])).

tff(c_1745,plain,(
    ! [B_343] : k2_zfmisc_1('#skF_10',B_343) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1672,c_1738])).

tff(c_1699,plain,(
    ! [A_330,D_332,B_331] :
      ( ~ v1_xboole_0(A_330)
      | ~ r2_hidden(D_332,k2_zfmisc_1(A_330,B_331)) ) ),
    inference(resolution,[status(thm)],[c_1695,c_2])).

tff(c_1756,plain,(
    ! [D_332] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_332,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_1699])).

tff(c_1783,plain,(
    ! [D_344] : ~ r2_hidden(D_344,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1756])).

tff(c_1807,plain,(
    ! [D_345,A_346] : ~ r2_hidden(D_345,k2_zfmisc_1(A_346,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_18,c_1783])).

tff(c_1835,plain,(
    ! [A_346] : k2_zfmisc_1(A_346,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1646,c_1807])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1659,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1630,c_1633,c_48])).

tff(c_1892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1659])).

tff(c_1893,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1629])).

tff(c_1896,plain,(
    ! [A_7] : r1_tarski('#skF_9',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_1621])).

tff(c_1895,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_1622])).

tff(c_1938,plain,(
    ! [B_356,A_357] :
      ( ~ r1_xboole_0(B_356,A_357)
      | ~ r1_tarski(B_356,A_357)
      | v1_xboole_0(B_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1943,plain,(
    ! [A_358] :
      ( ~ r1_tarski(A_358,'#skF_9')
      | v1_xboole_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_1895,c_1938])).

tff(c_1948,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1896,c_1943])).

tff(c_1897,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_1620])).

tff(c_1925,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_6])).

tff(c_1972,plain,(
    ! [A_375,B_376,D_377] :
      ( r2_hidden('#skF_7'(A_375,B_376,k2_zfmisc_1(A_375,B_376),D_377),A_375)
      | ~ r2_hidden(D_377,k2_zfmisc_1(A_375,B_376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1977,plain,(
    ! [A_378,D_379,B_380] :
      ( ~ v1_xboole_0(A_378)
      | ~ r2_hidden(D_379,k2_zfmisc_1(A_378,B_380)) ) ),
    inference(resolution,[status(thm)],[c_1972,c_2])).

tff(c_2015,plain,(
    ! [A_386,B_387] :
      ( ~ v1_xboole_0(A_386)
      | k2_zfmisc_1(A_386,B_387) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1925,c_1977])).

tff(c_2021,plain,(
    ! [B_387] : k2_zfmisc_1('#skF_9',B_387) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1948,c_2015])).

tff(c_1902,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_48])).

tff(c_1903,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1902])).

tff(c_1910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_1903])).

tff(c_1911,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1902])).

tff(c_1921,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_1911])).

tff(c_2024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2021,c_1921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:54:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.55  
% 3.04/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 3.04/1.56  
% 3.04/1.56  %Foreground sorts:
% 3.04/1.56  
% 3.04/1.56  
% 3.04/1.56  %Background operators:
% 3.04/1.56  
% 3.04/1.56  
% 3.04/1.56  %Foreground operators:
% 3.04/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.04/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.04/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.04/1.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.04/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.04/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.04/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.56  tff('#skF_12', type, '#skF_12': $i).
% 3.04/1.56  
% 3.32/1.58  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.32/1.58  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.58  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.32/1.58  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.32/1.58  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.32/1.58  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.32/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.32/1.58  tff(f_63, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.32/1.58  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.58  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.58  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.58  tff(c_486, plain, (![B_152, A_153]: (~r1_xboole_0(B_152, A_153) | ~r1_tarski(B_152, A_153) | v1_xboole_0(B_152))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_491, plain, (![A_154]: (~r1_tarski(A_154, k1_xboole_0) | v1_xboole_0(A_154))), inference(resolution, [status(thm)], [c_10, c_486])).
% 3.32/1.58  tff(c_496, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_491])).
% 3.32/1.58  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_70, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_44])).
% 3.32/1.58  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_58, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 3.32/1.58  tff(c_72, plain, (![B_56, A_57]: (~r1_xboole_0(B_56, A_57) | ~r1_tarski(B_56, A_57) | v1_xboole_0(B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_82, plain, (![A_58]: (~r1_tarski(A_58, k1_xboole_0) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_10, c_72])).
% 3.32/1.58  tff(c_87, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_82])).
% 3.32/1.58  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_77, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.32/1.58  tff(c_103, plain, (![A_71, B_72, C_73, D_74]: (r2_hidden(k4_tarski(A_71, B_72), k2_zfmisc_1(C_73, D_74)) | ~r2_hidden(B_72, D_74) | ~r2_hidden(A_71, C_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.32/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.58  tff(c_119, plain, (![C_75, D_76, B_77, A_78]: (~v1_xboole_0(k2_zfmisc_1(C_75, D_76)) | ~r2_hidden(B_77, D_76) | ~r2_hidden(A_78, C_75))), inference(resolution, [status(thm)], [c_103, c_2])).
% 3.32/1.58  tff(c_121, plain, (![B_77, A_78]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_77, '#skF_12') | ~r2_hidden(A_78, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_119])).
% 3.32/1.58  tff(c_123, plain, (![B_77, A_78]: (~r2_hidden(B_77, '#skF_12') | ~r2_hidden(A_78, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_121])).
% 3.32/1.58  tff(c_135, plain, (![A_82]: (~r2_hidden(A_82, '#skF_11'))), inference(splitLeft, [status(thm)], [c_123])).
% 3.32/1.58  tff(c_147, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_135])).
% 3.32/1.58  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_147])).
% 3.32/1.58  tff(c_156, plain, (![B_83]: (~r2_hidden(B_83, '#skF_12'))), inference(splitRight, [status(thm)], [c_123])).
% 3.32/1.58  tff(c_168, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_6, c_156])).
% 3.32/1.58  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_168])).
% 3.32/1.58  tff(c_175, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 3.32/1.58  tff(c_177, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_175])).
% 3.32/1.58  tff(c_181, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_6])).
% 3.32/1.58  tff(c_18, plain, (![A_11, B_12, D_38]: (r2_hidden('#skF_8'(A_11, B_12, k2_zfmisc_1(A_11, B_12), D_38), B_12) | ~r2_hidden(D_38, k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_183, plain, (![A_7]: (r1_tarski('#skF_10', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_8])).
% 3.32/1.58  tff(c_76, plain, (![A_8]: (~r1_tarski(A_8, k1_xboole_0) | v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_10, c_72])).
% 3.32/1.58  tff(c_198, plain, (![A_87]: (~r1_tarski(A_87, '#skF_10') | v1_xboole_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_76])).
% 3.32/1.58  tff(c_203, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_183, c_198])).
% 3.32/1.58  tff(c_229, plain, (![A_101, B_102, D_103]: (r2_hidden('#skF_7'(A_101, B_102, k2_zfmisc_1(A_101, B_102), D_103), A_101) | ~r2_hidden(D_103, k2_zfmisc_1(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_234, plain, (![A_104, D_105, B_106]: (~v1_xboole_0(A_104) | ~r2_hidden(D_105, k2_zfmisc_1(A_104, B_106)))), inference(resolution, [status(thm)], [c_229, c_2])).
% 3.32/1.58  tff(c_259, plain, (![A_109, B_110]: (~v1_xboole_0(A_109) | k2_zfmisc_1(A_109, B_110)='#skF_10')), inference(resolution, [status(thm)], [c_181, c_234])).
% 3.32/1.58  tff(c_276, plain, (![B_114]: (k2_zfmisc_1('#skF_10', B_114)='#skF_10')), inference(resolution, [status(thm)], [c_203, c_259])).
% 3.32/1.58  tff(c_233, plain, (![A_101, D_103, B_102]: (~v1_xboole_0(A_101) | ~r2_hidden(D_103, k2_zfmisc_1(A_101, B_102)))), inference(resolution, [status(thm)], [c_229, c_2])).
% 3.32/1.58  tff(c_287, plain, (![D_103]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_103, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_233])).
% 3.32/1.58  tff(c_310, plain, (![D_115]: (~r2_hidden(D_115, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_287])).
% 3.32/1.58  tff(c_334, plain, (![D_116, A_117]: (~r2_hidden(D_116, k2_zfmisc_1(A_117, '#skF_10')))), inference(resolution, [status(thm)], [c_18, c_310])).
% 3.32/1.58  tff(c_361, plain, (![A_117]: (k2_zfmisc_1(A_117, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_181, c_334])).
% 3.32/1.58  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_71, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.32/1.58  tff(c_178, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_71])).
% 3.32/1.58  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_178])).
% 3.32/1.58  tff(c_367, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_175])).
% 3.32/1.58  tff(c_375, plain, (![A_7]: (r1_tarski('#skF_9', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_8])).
% 3.32/1.58  tff(c_390, plain, (![A_121]: (~r1_tarski(A_121, '#skF_9') | v1_xboole_0(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_76])).
% 3.32/1.58  tff(c_395, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_375, c_390])).
% 3.32/1.58  tff(c_373, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_6])).
% 3.32/1.58  tff(c_422, plain, (![A_139, B_140, D_141]: (r2_hidden('#skF_7'(A_139, B_140, k2_zfmisc_1(A_139, B_140), D_141), A_139) | ~r2_hidden(D_141, k2_zfmisc_1(A_139, B_140)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_427, plain, (![A_142, D_143, B_144]: (~v1_xboole_0(A_142) | ~r2_hidden(D_143, k2_zfmisc_1(A_142, B_144)))), inference(resolution, [status(thm)], [c_422, c_2])).
% 3.32/1.58  tff(c_465, plain, (![A_150, B_151]: (~v1_xboole_0(A_150) | k2_zfmisc_1(A_150, B_151)='#skF_9')), inference(resolution, [status(thm)], [c_373, c_427])).
% 3.32/1.58  tff(c_471, plain, (![B_151]: (k2_zfmisc_1('#skF_9', B_151)='#skF_9')), inference(resolution, [status(thm)], [c_395, c_465])).
% 3.32/1.58  tff(c_370, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_71])).
% 3.32/1.58  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_471, c_370])).
% 3.32/1.58  tff(c_476, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.32/1.58  tff(c_520, plain, (![A_171, B_172, C_173, D_174]: (r2_hidden(k4_tarski(A_171, B_172), k2_zfmisc_1(C_173, D_174)) | ~r2_hidden(B_172, D_174) | ~r2_hidden(A_171, C_173))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.32/1.58  tff(c_539, plain, (![C_175, D_176, B_177, A_178]: (~v1_xboole_0(k2_zfmisc_1(C_175, D_176)) | ~r2_hidden(B_177, D_176) | ~r2_hidden(A_178, C_175))), inference(resolution, [status(thm)], [c_520, c_2])).
% 3.32/1.58  tff(c_541, plain, (![B_177, A_178]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_177, '#skF_10') | ~r2_hidden(A_178, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_539])).
% 3.32/1.58  tff(c_545, plain, (![B_177, A_178]: (~r2_hidden(B_177, '#skF_10') | ~r2_hidden(A_178, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_541])).
% 3.32/1.58  tff(c_550, plain, (![A_179]: (~r2_hidden(A_179, '#skF_9'))), inference(splitLeft, [status(thm)], [c_545])).
% 3.32/1.58  tff(c_560, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_550])).
% 3.32/1.58  tff(c_590, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_70])).
% 3.32/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.58  tff(c_593, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_58])).
% 3.32/1.58  tff(c_475, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.32/1.58  tff(c_543, plain, (![B_177, A_178]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_177, '#skF_12') | ~r2_hidden(A_178, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_539])).
% 3.32/1.58  tff(c_547, plain, (![B_177, A_178]: (~r2_hidden(B_177, '#skF_12') | ~r2_hidden(A_178, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_543])).
% 3.32/1.58  tff(c_852, plain, (![A_201]: (~r2_hidden(A_201, '#skF_11'))), inference(splitLeft, [status(thm)], [c_547])).
% 3.32/1.58  tff(c_874, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_852])).
% 3.32/1.58  tff(c_59, plain, (![A_53]: (r2_hidden('#skF_2'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.58  tff(c_63, plain, (![A_53]: (~v1_xboole_0(A_53) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_59, c_2])).
% 3.32/1.58  tff(c_591, plain, (![A_53]: (~v1_xboole_0(A_53) | A_53='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_63])).
% 3.32/1.58  tff(c_879, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_874, c_591])).
% 3.32/1.58  tff(c_883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_593, c_879])).
% 3.32/1.58  tff(c_885, plain, (![B_202]: (~r2_hidden(B_202, '#skF_12'))), inference(splitRight, [status(thm)], [c_547])).
% 3.32/1.58  tff(c_907, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_4, c_885])).
% 3.32/1.58  tff(c_910, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_907, c_591])).
% 3.32/1.58  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_590, c_910])).
% 3.32/1.58  tff(c_917, plain, (![B_203]: (~r2_hidden(B_203, '#skF_10'))), inference(splitRight, [status(thm)], [c_545])).
% 3.32/1.58  tff(c_927, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_917])).
% 3.32/1.58  tff(c_958, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_927, c_70])).
% 3.32/1.58  tff(c_961, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_927, c_58])).
% 3.32/1.58  tff(c_1218, plain, (![A_225]: (~r2_hidden(A_225, '#skF_11'))), inference(splitLeft, [status(thm)], [c_547])).
% 3.32/1.58  tff(c_1238, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1218])).
% 3.32/1.58  tff(c_959, plain, (![A_53]: (~v1_xboole_0(A_53) | A_53='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_927, c_63])).
% 3.32/1.58  tff(c_1241, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_1238, c_959])).
% 3.32/1.58  tff(c_1245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_961, c_1241])).
% 3.32/1.58  tff(c_1247, plain, (![B_226]: (~r2_hidden(B_226, '#skF_12'))), inference(splitRight, [status(thm)], [c_547])).
% 3.32/1.58  tff(c_1267, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_4, c_1247])).
% 3.32/1.58  tff(c_1270, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1267, c_959])).
% 3.32/1.58  tff(c_1274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_958, c_1270])).
% 3.32/1.58  tff(c_1276, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_44])).
% 3.32/1.58  tff(c_1278, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_6])).
% 3.32/1.58  tff(c_1280, plain, (![A_7]: (r1_tarski('#skF_12', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_8])).
% 3.32/1.58  tff(c_1281, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_10])).
% 3.32/1.58  tff(c_1404, plain, (![B_265, A_266]: (~r1_xboole_0(B_265, A_266) | ~r1_tarski(B_265, A_266) | v1_xboole_0(B_265))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_1409, plain, (![A_267]: (~r1_tarski(A_267, '#skF_12') | v1_xboole_0(A_267))), inference(resolution, [status(thm)], [c_1281, c_1404])).
% 3.32/1.58  tff(c_1414, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_1280, c_1409])).
% 3.32/1.58  tff(c_1438, plain, (![A_284, B_285, D_286]: (r2_hidden('#skF_7'(A_284, B_285, k2_zfmisc_1(A_284, B_285), D_286), A_284) | ~r2_hidden(D_286, k2_zfmisc_1(A_284, B_285)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_1443, plain, (![A_287, D_288, B_289]: (~v1_xboole_0(A_287) | ~r2_hidden(D_288, k2_zfmisc_1(A_287, B_289)))), inference(resolution, [status(thm)], [c_1438, c_2])).
% 3.32/1.58  tff(c_1481, plain, (![A_295, B_296]: (~v1_xboole_0(A_295) | k2_zfmisc_1(A_295, B_296)='#skF_12')), inference(resolution, [status(thm)], [c_1278, c_1443])).
% 3.32/1.58  tff(c_1488, plain, (![B_297]: (k2_zfmisc_1('#skF_12', B_297)='#skF_12')), inference(resolution, [status(thm)], [c_1414, c_1481])).
% 3.32/1.58  tff(c_1442, plain, (![A_284, D_286, B_285]: (~v1_xboole_0(A_284) | ~r2_hidden(D_286, k2_zfmisc_1(A_284, B_285)))), inference(resolution, [status(thm)], [c_1438, c_2])).
% 3.32/1.58  tff(c_1499, plain, (![D_286]: (~v1_xboole_0('#skF_12') | ~r2_hidden(D_286, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1488, c_1442])).
% 3.32/1.58  tff(c_1545, plain, (![D_301]: (~r2_hidden(D_301, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1499])).
% 3.32/1.58  tff(c_1576, plain, (![D_302, A_303]: (~r2_hidden(D_302, k2_zfmisc_1(A_303, '#skF_12')))), inference(resolution, [status(thm)], [c_18, c_1545])).
% 3.32/1.58  tff(c_1613, plain, (![A_303]: (k2_zfmisc_1(A_303, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1278, c_1576])).
% 3.32/1.58  tff(c_1304, plain, (![B_231, A_232]: (~r1_xboole_0(B_231, A_232) | ~r1_tarski(B_231, A_232) | v1_xboole_0(B_231))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_1309, plain, (![A_233]: (~r1_tarski(A_233, '#skF_12') | v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_1281, c_1304])).
% 3.32/1.58  tff(c_1314, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_1280, c_1309])).
% 3.32/1.58  tff(c_1337, plain, (![A_250, B_251, D_252]: (r2_hidden('#skF_7'(A_250, B_251, k2_zfmisc_1(A_250, B_251), D_252), A_250) | ~r2_hidden(D_252, k2_zfmisc_1(A_250, B_251)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_1342, plain, (![A_253, D_254, B_255]: (~v1_xboole_0(A_253) | ~r2_hidden(D_254, k2_zfmisc_1(A_253, B_255)))), inference(resolution, [status(thm)], [c_1337, c_2])).
% 3.32/1.58  tff(c_1380, plain, (![A_261, B_262]: (~v1_xboole_0(A_261) | k2_zfmisc_1(A_261, B_262)='#skF_12')), inference(resolution, [status(thm)], [c_1278, c_1342])).
% 3.32/1.58  tff(c_1386, plain, (![B_262]: (k2_zfmisc_1('#skF_12', B_262)='#skF_12')), inference(resolution, [status(thm)], [c_1314, c_1380])).
% 3.32/1.58  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_1290, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1276, c_1276, c_46])).
% 3.32/1.58  tff(c_1291, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_1290])).
% 3.32/1.58  tff(c_1275, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.32/1.58  tff(c_1288, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1275])).
% 3.32/1.58  tff(c_1292, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_1288])).
% 3.32/1.58  tff(c_1389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1292])).
% 3.32/1.58  tff(c_1390, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_1290])).
% 3.32/1.58  tff(c_1393, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1288])).
% 3.32/1.58  tff(c_1618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1393])).
% 3.32/1.58  tff(c_1620, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 3.32/1.58  tff(c_1619, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 3.32/1.58  tff(c_1629, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1620, c_1619])).
% 3.32/1.58  tff(c_1630, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1629])).
% 3.32/1.58  tff(c_1633, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1620])).
% 3.32/1.58  tff(c_1646, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_6])).
% 3.32/1.58  tff(c_1621, plain, (![A_7]: (r1_tarski('#skF_11', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_8])).
% 3.32/1.58  tff(c_1632, plain, (![A_7]: (r1_tarski('#skF_10', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1621])).
% 3.32/1.58  tff(c_1622, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_10])).
% 3.32/1.58  tff(c_1631, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1622])).
% 3.32/1.58  tff(c_1661, plain, (![B_311, A_312]: (~r1_xboole_0(B_311, A_312) | ~r1_tarski(B_311, A_312) | v1_xboole_0(B_311))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_1667, plain, (![A_313]: (~r1_tarski(A_313, '#skF_10') | v1_xboole_0(A_313))), inference(resolution, [status(thm)], [c_1631, c_1661])).
% 3.32/1.58  tff(c_1672, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_1632, c_1667])).
% 3.32/1.58  tff(c_1695, plain, (![A_330, B_331, D_332]: (r2_hidden('#skF_7'(A_330, B_331, k2_zfmisc_1(A_330, B_331), D_332), A_330) | ~r2_hidden(D_332, k2_zfmisc_1(A_330, B_331)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_1700, plain, (![A_333, D_334, B_335]: (~v1_xboole_0(A_333) | ~r2_hidden(D_334, k2_zfmisc_1(A_333, B_335)))), inference(resolution, [status(thm)], [c_1695, c_2])).
% 3.32/1.58  tff(c_1738, plain, (![A_341, B_342]: (~v1_xboole_0(A_341) | k2_zfmisc_1(A_341, B_342)='#skF_10')), inference(resolution, [status(thm)], [c_1646, c_1700])).
% 3.32/1.58  tff(c_1745, plain, (![B_343]: (k2_zfmisc_1('#skF_10', B_343)='#skF_10')), inference(resolution, [status(thm)], [c_1672, c_1738])).
% 3.32/1.58  tff(c_1699, plain, (![A_330, D_332, B_331]: (~v1_xboole_0(A_330) | ~r2_hidden(D_332, k2_zfmisc_1(A_330, B_331)))), inference(resolution, [status(thm)], [c_1695, c_2])).
% 3.32/1.58  tff(c_1756, plain, (![D_332]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_332, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_1699])).
% 3.32/1.58  tff(c_1783, plain, (![D_344]: (~r2_hidden(D_344, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1756])).
% 3.32/1.58  tff(c_1807, plain, (![D_345, A_346]: (~r2_hidden(D_345, k2_zfmisc_1(A_346, '#skF_10')))), inference(resolution, [status(thm)], [c_18, c_1783])).
% 3.32/1.58  tff(c_1835, plain, (![A_346]: (k2_zfmisc_1(A_346, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1646, c_1807])).
% 3.32/1.58  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_1659, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1630, c_1633, c_48])).
% 3.32/1.58  tff(c_1892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1659])).
% 3.32/1.58  tff(c_1893, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1629])).
% 3.32/1.58  tff(c_1896, plain, (![A_7]: (r1_tarski('#skF_9', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_1621])).
% 3.32/1.58  tff(c_1895, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_1622])).
% 3.32/1.58  tff(c_1938, plain, (![B_356, A_357]: (~r1_xboole_0(B_356, A_357) | ~r1_tarski(B_356, A_357) | v1_xboole_0(B_356))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_1943, plain, (![A_358]: (~r1_tarski(A_358, '#skF_9') | v1_xboole_0(A_358))), inference(resolution, [status(thm)], [c_1895, c_1938])).
% 3.32/1.58  tff(c_1948, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_1896, c_1943])).
% 3.32/1.58  tff(c_1897, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_1620])).
% 3.32/1.58  tff(c_1925, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1897, c_6])).
% 3.32/1.58  tff(c_1972, plain, (![A_375, B_376, D_377]: (r2_hidden('#skF_7'(A_375, B_376, k2_zfmisc_1(A_375, B_376), D_377), A_375) | ~r2_hidden(D_377, k2_zfmisc_1(A_375, B_376)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_1977, plain, (![A_378, D_379, B_380]: (~v1_xboole_0(A_378) | ~r2_hidden(D_379, k2_zfmisc_1(A_378, B_380)))), inference(resolution, [status(thm)], [c_1972, c_2])).
% 3.32/1.58  tff(c_2015, plain, (![A_386, B_387]: (~v1_xboole_0(A_386) | k2_zfmisc_1(A_386, B_387)='#skF_9')), inference(resolution, [status(thm)], [c_1925, c_1977])).
% 3.32/1.58  tff(c_2021, plain, (![B_387]: (k2_zfmisc_1('#skF_9', B_387)='#skF_9')), inference(resolution, [status(thm)], [c_1948, c_2015])).
% 3.32/1.58  tff(c_1902, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_48])).
% 3.32/1.58  tff(c_1903, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_1902])).
% 3.32/1.58  tff(c_1910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1897, c_1903])).
% 3.32/1.58  tff(c_1911, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1902])).
% 3.32/1.58  tff(c_1921, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1897, c_1911])).
% 3.32/1.58  tff(c_2024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2021, c_1921])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 401
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 14
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 117
% 3.32/1.58  #Demod        : 213
% 3.32/1.58  #Tautology    : 121
% 3.32/1.58  #SimpNegUnit  : 38
% 3.32/1.58  #BackRed      : 78
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.59  Preprocessing        : 0.31
% 3.32/1.59  Parsing              : 0.16
% 3.32/1.59  CNF conversion       : 0.03
% 3.32/1.59  Main loop            : 0.45
% 3.32/1.59  Inferencing          : 0.17
% 3.32/1.59  Reduction            : 0.12
% 3.32/1.59  Demodulation         : 0.08
% 3.32/1.59  BG Simplification    : 0.03
% 3.32/1.59  Subsumption          : 0.08
% 3.32/1.59  Abstraction          : 0.02
% 3.32/1.59  MUC search           : 0.00
% 3.32/1.59  Cooper               : 0.00
% 3.32/1.59  Total                : 0.82
% 3.32/1.59  Index Insertion      : 0.00
% 3.32/1.59  Index Deletion       : 0.00
% 3.32/1.59  Index Matching       : 0.00
% 3.32/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
