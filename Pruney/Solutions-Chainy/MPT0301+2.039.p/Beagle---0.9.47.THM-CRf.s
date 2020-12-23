%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  201 (1141 expanded)
%              Number of leaves         :   24 ( 334 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 (2557 expanded)
%              Number of equality atoms :  103 (1560 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_14,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_125,plain,(
    ! [E_59,F_60,A_61,B_62] :
      ( r2_hidden(k4_tarski(E_59,F_60),k2_zfmisc_1(A_61,B_62))
      | ~ r2_hidden(F_60,B_62)
      | ~ r2_hidden(E_59,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,(
    ! [E_63,F_64] :
      ( r2_hidden(k4_tarski(E_63,F_64),k1_xboole_0)
      | ~ r2_hidden(F_64,'#skF_11')
      | ~ r2_hidden(E_63,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_125])).

tff(c_16,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(A_51,B_52)
      | ~ r2_hidden(A_51,C_53)
      | r2_hidden(A_51,k5_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_51,A_6] :
      ( r2_hidden(A_51,A_6)
      | ~ r2_hidden(A_51,k1_xboole_0)
      | r2_hidden(A_51,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_134,plain,(
    ! [E_63,F_64,A_6] :
      ( r2_hidden(k4_tarski(E_63,F_64),A_6)
      | ~ r2_hidden(F_64,'#skF_11')
      | ~ r2_hidden(E_63,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_129,c_104])).

tff(c_80,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_hidden(A_46,C_47)
      | ~ r2_hidden(A_46,B_48)
      | ~ r2_hidden(A_46,k5_xboole_0(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_46,A_6] :
      ( ~ r2_hidden(A_46,k1_xboole_0)
      | ~ r2_hidden(A_46,A_6)
      | ~ r2_hidden(A_46,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_80])).

tff(c_155,plain,(
    ! [E_68,F_69,A_70] :
      ( ~ r2_hidden(k4_tarski(E_68,F_69),A_70)
      | ~ r2_hidden(F_69,'#skF_11')
      | ~ r2_hidden(E_68,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_129,c_87])).

tff(c_170,plain,(
    ! [F_64,E_63] :
      ( ~ r2_hidden(F_64,'#skF_11')
      | ~ r2_hidden(E_63,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_134,c_155])).

tff(c_175,plain,(
    ! [E_71] : ~ r2_hidden(E_71,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_179])).

tff(c_185,plain,(
    ! [F_72] : ~ r2_hidden(F_72,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_189,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_189])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_196,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_199,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_14])).

tff(c_272,plain,(
    ! [A_95,B_96,D_97] :
      ( r2_hidden('#skF_7'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97),B_96)
      | ~ r2_hidden(D_97,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_9') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_16])).

tff(c_240,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden(A_83,B_84)
      | ~ r2_hidden(A_83,C_85)
      | r2_hidden(A_83,k5_xboole_0(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    ! [A_83,A_6] :
      ( r2_hidden(A_83,A_6)
      | ~ r2_hidden(A_83,'#skF_9')
      | r2_hidden(A_83,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_240])).

tff(c_287,plain,(
    ! [A_95,D_97,A_6] :
      ( r2_hidden('#skF_7'(A_95,'#skF_9',k2_zfmisc_1(A_95,'#skF_9'),D_97),A_6)
      | ~ r2_hidden(D_97,k2_zfmisc_1(A_95,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_272,c_246])).

tff(c_217,plain,(
    ! [A_75,C_76,B_77] :
      ( ~ r2_hidden(A_75,C_76)
      | ~ r2_hidden(A_75,B_77)
      | ~ r2_hidden(A_75,k5_xboole_0(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_75,A_6] :
      ( ~ r2_hidden(A_75,'#skF_9')
      | ~ r2_hidden(A_75,A_6)
      | ~ r2_hidden(A_75,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_217])).

tff(c_367,plain,(
    ! [A_110,D_111,A_112] :
      ( ~ r2_hidden('#skF_7'(A_110,'#skF_9',k2_zfmisc_1(A_110,'#skF_9'),D_111),A_112)
      | ~ r2_hidden(D_111,k2_zfmisc_1(A_110,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_272,c_224])).

tff(c_387,plain,(
    ! [D_113,A_114] : ~ r2_hidden(D_113,k2_zfmisc_1(A_114,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_287,c_367])).

tff(c_416,plain,(
    ! [A_114] : k2_zfmisc_1(A_114,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_199,c_387])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_65,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_198,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_65])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_198])).

tff(c_462,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_467,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_14])).

tff(c_540,plain,(
    ! [A_140,B_141,D_142] :
      ( r2_hidden('#skF_6'(A_140,B_141,k2_zfmisc_1(A_140,B_141),D_142),A_140)
      | ~ r2_hidden(D_142,k2_zfmisc_1(A_140,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_470,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_8') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_16])).

tff(c_508,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden(A_128,B_129)
      | ~ r2_hidden(A_128,C_130)
      | r2_hidden(A_128,k5_xboole_0(B_129,C_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_514,plain,(
    ! [A_128,A_6] :
      ( r2_hidden(A_128,A_6)
      | ~ r2_hidden(A_128,'#skF_8')
      | r2_hidden(A_128,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_508])).

tff(c_556,plain,(
    ! [B_141,D_142,A_6] :
      ( r2_hidden('#skF_6'('#skF_8',B_141,k2_zfmisc_1('#skF_8',B_141),D_142),A_6)
      | ~ r2_hidden(D_142,k2_zfmisc_1('#skF_8',B_141)) ) ),
    inference(resolution,[status(thm)],[c_540,c_514])).

tff(c_489,plain,(
    ! [A_123,C_124,B_125] :
      ( ~ r2_hidden(A_123,C_124)
      | ~ r2_hidden(A_123,B_125)
      | ~ r2_hidden(A_123,k5_xboole_0(B_125,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_499,plain,(
    ! [A_123,A_6] :
      ( ~ r2_hidden(A_123,'#skF_8')
      | ~ r2_hidden(A_123,A_6)
      | ~ r2_hidden(A_123,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_489])).

tff(c_628,plain,(
    ! [B_152,D_153,A_154] :
      ( ~ r2_hidden('#skF_6'('#skF_8',B_152,k2_zfmisc_1('#skF_8',B_152),D_153),A_154)
      | ~ r2_hidden(D_153,k2_zfmisc_1('#skF_8',B_152)) ) ),
    inference(resolution,[status(thm)],[c_540,c_499])).

tff(c_648,plain,(
    ! [D_155,B_156] : ~ r2_hidden(D_155,k2_zfmisc_1('#skF_8',B_156)) ),
    inference(resolution,[status(thm)],[c_556,c_628])).

tff(c_678,plain,(
    ! [B_156] : k2_zfmisc_1('#skF_8',B_156) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_467,c_648])).

tff(c_466,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_65])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_466])).

tff(c_684,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_748,plain,(
    ! [E_173,F_174,A_175,B_176] :
      ( r2_hidden(k4_tarski(E_173,F_174),k2_zfmisc_1(A_175,B_176))
      | ~ r2_hidden(F_174,B_176)
      | ~ r2_hidden(E_173,A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_751,plain,(
    ! [E_173,F_174] :
      ( r2_hidden(k4_tarski(E_173,F_174),k1_xboole_0)
      | ~ r2_hidden(F_174,'#skF_9')
      | ~ r2_hidden(E_173,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_748])).

tff(c_755,plain,(
    ! [E_177,F_178] :
      ( r2_hidden(k4_tarski(E_177,F_178),k1_xboole_0)
      | ~ r2_hidden(F_178,'#skF_9')
      | ~ r2_hidden(E_177,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_748])).

tff(c_725,plain,(
    ! [A_168,C_169,B_170] :
      ( ~ r2_hidden(A_168,C_169)
      | ~ r2_hidden(A_168,B_170)
      | ~ r2_hidden(A_168,k5_xboole_0(B_170,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_738,plain,(
    ! [A_168,A_6] :
      ( ~ r2_hidden(A_168,k1_xboole_0)
      | ~ r2_hidden(A_168,A_6)
      | ~ r2_hidden(A_168,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_725])).

tff(c_798,plain,(
    ! [E_186,F_187,A_188] :
      ( ~ r2_hidden(k4_tarski(E_186,F_187),A_188)
      | ~ r2_hidden(F_187,'#skF_9')
      | ~ r2_hidden(E_186,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_755,c_738])).

tff(c_817,plain,(
    ! [F_174,E_173] :
      ( ~ r2_hidden(F_174,'#skF_9')
      | ~ r2_hidden(E_173,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_751,c_798])).

tff(c_823,plain,(
    ! [E_189] : ~ r2_hidden(E_189,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_833,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_14,c_823])).

tff(c_841,plain,(
    '#skF_11' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_63])).

tff(c_840,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_14])).

tff(c_842,plain,(
    '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_62])).

tff(c_821,plain,(
    ! [E_173] : ~ r2_hidden(E_173,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_683,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_754,plain,(
    ! [E_173,F_174] :
      ( r2_hidden(k4_tarski(E_173,F_174),k1_xboole_0)
      | ~ r2_hidden(F_174,'#skF_11')
      | ~ r2_hidden(E_173,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_748])).

tff(c_834,plain,(
    ! [E_173,F_174] :
      ( r2_hidden(k4_tarski(E_173,F_174),'#skF_8')
      | ~ r2_hidden(F_174,'#skF_11')
      | ~ r2_hidden(E_173,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_754])).

tff(c_844,plain,(
    ! [F_174,E_173] :
      ( ~ r2_hidden(F_174,'#skF_11')
      | ~ r2_hidden(E_173,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_821,c_834])).

tff(c_1066,plain,(
    ! [E_204] : ~ r2_hidden(E_204,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_1076,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_840,c_1066])).

tff(c_1089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_1076])).

tff(c_1091,plain,(
    ! [F_205] : ~ r2_hidden(F_205,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_1101,plain,(
    '#skF_11' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_840,c_1091])).

tff(c_1114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_1101])).

tff(c_1139,plain,(
    ! [F_209] : ~ r2_hidden(F_209,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_1149,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14,c_1139])).

tff(c_1158,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_63])).

tff(c_1501,plain,(
    ! [A_235] :
      ( r2_hidden('#skF_1'(A_235),A_235)
      | A_235 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_14])).

tff(c_1159,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_62])).

tff(c_1416,plain,(
    ! [A_229] :
      ( r2_hidden('#skF_1'(A_229),A_229)
      | A_229 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_14])).

tff(c_1115,plain,(
    ! [F_174] : ~ r2_hidden(F_174,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_1150,plain,(
    ! [E_173,F_174] :
      ( r2_hidden(k4_tarski(E_173,F_174),'#skF_9')
      | ~ r2_hidden(F_174,'#skF_11')
      | ~ r2_hidden(E_173,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_754])).

tff(c_1161,plain,(
    ! [F_174,E_173] :
      ( ~ r2_hidden(F_174,'#skF_11')
      | ~ r2_hidden(E_173,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1115,c_1150])).

tff(c_1295,plain,(
    ! [E_173] : ~ r2_hidden(E_173,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1161])).

tff(c_1428,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1416,c_1295])).

tff(c_1454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1159,c_1428])).

tff(c_1455,plain,(
    ! [F_174] : ~ r2_hidden(F_174,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_1161])).

tff(c_1513,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1501,c_1455])).

tff(c_1539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1158,c_1513])).

tff(c_1541,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1540,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1557,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1541,c_1540])).

tff(c_1558,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1557])).

tff(c_1561,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1541])).

tff(c_1586,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_14])).

tff(c_22,plain,(
    ! [A_7,B_8,D_34] :
      ( r2_hidden('#skF_7'(A_7,B_8,k2_zfmisc_1(A_7,B_8),D_34),B_8)
      | ~ r2_hidden(D_34,k2_zfmisc_1(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1645,plain,(
    ! [A_259,B_260,D_261] :
      ( r2_hidden('#skF_6'(A_259,B_260,k2_zfmisc_1(A_259,B_260),D_261),A_259)
      | ~ r2_hidden(D_261,k2_zfmisc_1(A_259,B_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1543,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_11') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_16])).

tff(c_1559,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_9') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1543])).

tff(c_1613,plain,(
    ! [A_247,B_248,C_249] :
      ( r2_hidden(A_247,B_248)
      | ~ r2_hidden(A_247,C_249)
      | r2_hidden(A_247,k5_xboole_0(B_248,C_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1619,plain,(
    ! [A_247,A_6] :
      ( r2_hidden(A_247,A_6)
      | ~ r2_hidden(A_247,'#skF_9')
      | r2_hidden(A_247,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_1613])).

tff(c_1661,plain,(
    ! [B_260,D_261,A_6] :
      ( r2_hidden('#skF_6'('#skF_9',B_260,k2_zfmisc_1('#skF_9',B_260),D_261),A_6)
      | ~ r2_hidden(D_261,k2_zfmisc_1('#skF_9',B_260)) ) ),
    inference(resolution,[status(thm)],[c_1645,c_1619])).

tff(c_1590,plain,(
    ! [A_239,C_240,B_241] :
      ( ~ r2_hidden(A_239,C_240)
      | ~ r2_hidden(A_239,B_241)
      | ~ r2_hidden(A_239,k5_xboole_0(B_241,C_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1597,plain,(
    ! [A_239,A_6] :
      ( ~ r2_hidden(A_239,'#skF_9')
      | ~ r2_hidden(A_239,A_6)
      | ~ r2_hidden(A_239,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_1590])).

tff(c_1733,plain,(
    ! [B_271,D_272,A_273] :
      ( ~ r2_hidden('#skF_6'('#skF_9',B_271,k2_zfmisc_1('#skF_9',B_271),D_272),A_273)
      | ~ r2_hidden(D_272,k2_zfmisc_1('#skF_9',B_271)) ) ),
    inference(resolution,[status(thm)],[c_1645,c_1597])).

tff(c_1753,plain,(
    ! [D_274,B_275] : ~ r2_hidden(D_274,k2_zfmisc_1('#skF_9',B_275)) ),
    inference(resolution,[status(thm)],[c_1661,c_1733])).

tff(c_1783,plain,(
    ! [B_275] : k2_zfmisc_1('#skF_9',B_275) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1586,c_1753])).

tff(c_1749,plain,(
    ! [D_261,B_260] : ~ r2_hidden(D_261,k2_zfmisc_1('#skF_9',B_260)) ),
    inference(resolution,[status(thm)],[c_1661,c_1733])).

tff(c_1803,plain,(
    ! [D_277] : ~ r2_hidden(D_277,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1749])).

tff(c_1845,plain,(
    ! [D_281,A_282] : ~ r2_hidden(D_281,k2_zfmisc_1(A_282,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_22,c_1803])).

tff(c_1883,plain,(
    ! [A_282] : k2_zfmisc_1(A_282,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1586,c_1845])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1566,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_42])).

tff(c_1567,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1567,c_1561])).

tff(c_1569,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_1585,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_1569])).

tff(c_1887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1585])).

tff(c_1888,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_1895,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1541])).

tff(c_1914,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_14])).

tff(c_1974,plain,(
    ! [A_305,B_306,D_307] :
      ( r2_hidden('#skF_6'(A_305,B_306,k2_zfmisc_1(A_305,B_306),D_307),A_305)
      | ~ r2_hidden(D_307,k2_zfmisc_1(A_305,B_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1893,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_8') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1543])).

tff(c_1943,plain,(
    ! [A_293,B_294,C_295] :
      ( r2_hidden(A_293,B_294)
      | ~ r2_hidden(A_293,C_295)
      | r2_hidden(A_293,k5_xboole_0(B_294,C_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1952,plain,(
    ! [A_293,A_6] :
      ( r2_hidden(A_293,A_6)
      | ~ r2_hidden(A_293,'#skF_8')
      | r2_hidden(A_293,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_1943])).

tff(c_1989,plain,(
    ! [B_306,D_307,A_6] :
      ( r2_hidden('#skF_6'('#skF_8',B_306,k2_zfmisc_1('#skF_8',B_306),D_307),A_6)
      | ~ r2_hidden(D_307,k2_zfmisc_1('#skF_8',B_306)) ) ),
    inference(resolution,[status(thm)],[c_1974,c_1952])).

tff(c_1928,plain,(
    ! [A_288,C_289,B_290] :
      ( ~ r2_hidden(A_288,C_289)
      | ~ r2_hidden(A_288,B_290)
      | ~ r2_hidden(A_288,k5_xboole_0(B_290,C_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1935,plain,(
    ! [A_288,A_6] :
      ( ~ r2_hidden(A_288,'#skF_8')
      | ~ r2_hidden(A_288,A_6)
      | ~ r2_hidden(A_288,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_1928])).

tff(c_2081,plain,(
    ! [B_320,D_321,A_322] :
      ( ~ r2_hidden('#skF_6'('#skF_8',B_320,k2_zfmisc_1('#skF_8',B_320),D_321),A_322)
      | ~ r2_hidden(D_321,k2_zfmisc_1('#skF_8',B_320)) ) ),
    inference(resolution,[status(thm)],[c_1974,c_1935])).

tff(c_2101,plain,(
    ! [D_323,B_324] : ~ r2_hidden(D_323,k2_zfmisc_1('#skF_8',B_324)) ),
    inference(resolution,[status(thm)],[c_1989,c_2081])).

tff(c_2135,plain,(
    ! [B_324] : k2_zfmisc_1('#skF_8',B_324) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1914,c_2101])).

tff(c_1891,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1541,c_42])).

tff(c_1892,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1891])).

tff(c_2139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_1892])).

tff(c_2141,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2140,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2147,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2141,c_2141,c_2140])).

tff(c_2148,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2147])).

tff(c_2149,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_2141])).

tff(c_2171,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_14])).

tff(c_2231,plain,(
    ! [A_347,B_348,D_349] :
      ( r2_hidden('#skF_7'(A_347,B_348,k2_zfmisc_1(A_347,B_348),D_349),B_348)
      | ~ r2_hidden(D_349,k2_zfmisc_1(A_347,B_348)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2142,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_10') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2141,c_16])).

tff(c_2158,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_9') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_2142])).

tff(c_2207,plain,(
    ! [A_338,C_339,B_340] :
      ( ~ r2_hidden(A_338,C_339)
      | ~ r2_hidden(A_338,B_340)
      | ~ r2_hidden(A_338,k5_xboole_0(B_340,C_339)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2220,plain,(
    ! [A_338,A_6] :
      ( ~ r2_hidden(A_338,'#skF_9')
      | ~ r2_hidden(A_338,A_6)
      | ~ r2_hidden(A_338,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_2207])).

tff(c_2269,plain,(
    ! [A_353,D_354,A_355] :
      ( ~ r2_hidden('#skF_7'(A_353,'#skF_9',k2_zfmisc_1(A_353,'#skF_9'),D_354),A_355)
      | ~ r2_hidden(D_354,k2_zfmisc_1(A_353,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_2231,c_2220])).

tff(c_2304,plain,(
    ! [D_359,A_360] : ~ r2_hidden(D_359,k2_zfmisc_1(A_360,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_22,c_2269])).

tff(c_2329,plain,(
    ! [A_360] : k2_zfmisc_1(A_360,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2171,c_2304])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2169,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_2148,c_2149,c_46])).

tff(c_2333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2169])).

tff(c_2334,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2147])).

tff(c_2336,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2141])).

tff(c_2372,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2336,c_14])).

tff(c_2432,plain,(
    ! [A_383,B_384,D_385] :
      ( r2_hidden('#skF_6'(A_383,B_384,k2_zfmisc_1(A_383,B_384),D_385),A_383)
      | ~ r2_hidden(D_385,k2_zfmisc_1(A_383,B_384)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2359,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_8') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2142])).

tff(c_2395,plain,(
    ! [A_369,B_370,C_371] :
      ( r2_hidden(A_369,B_370)
      | ~ r2_hidden(A_369,C_371)
      | r2_hidden(A_369,k5_xboole_0(B_370,C_371)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2404,plain,(
    ! [A_369,A_6] :
      ( r2_hidden(A_369,A_6)
      | ~ r2_hidden(A_369,'#skF_8')
      | r2_hidden(A_369,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2359,c_2395])).

tff(c_2447,plain,(
    ! [B_384,D_385,A_6] :
      ( r2_hidden('#skF_6'('#skF_8',B_384,k2_zfmisc_1('#skF_8',B_384),D_385),A_6)
      | ~ r2_hidden(D_385,k2_zfmisc_1('#skF_8',B_384)) ) ),
    inference(resolution,[status(thm)],[c_2432,c_2404])).

tff(c_2451,plain,(
    ! [A_386,B_387,D_388] :
      ( r2_hidden('#skF_7'(A_386,B_387,k2_zfmisc_1(A_386,B_387),D_388),B_387)
      | ~ r2_hidden(D_388,k2_zfmisc_1(A_386,B_387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2466,plain,(
    ! [A_386,D_388,A_6] :
      ( r2_hidden('#skF_7'(A_386,'#skF_8',k2_zfmisc_1(A_386,'#skF_8'),D_388),A_6)
      | ~ r2_hidden(D_388,k2_zfmisc_1(A_386,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2451,c_2404])).

tff(c_2386,plain,(
    ! [A_366,C_367,B_368] :
      ( ~ r2_hidden(A_366,C_367)
      | ~ r2_hidden(A_366,B_368)
      | ~ r2_hidden(A_366,k5_xboole_0(B_368,C_367)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2393,plain,(
    ! [A_366,A_6] :
      ( ~ r2_hidden(A_366,'#skF_8')
      | ~ r2_hidden(A_366,A_6)
      | ~ r2_hidden(A_366,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2359,c_2386])).

tff(c_2508,plain,(
    ! [A_395,D_396,A_397] :
      ( ~ r2_hidden('#skF_7'(A_395,'#skF_8',k2_zfmisc_1(A_395,'#skF_8'),D_396),A_397)
      | ~ r2_hidden(D_396,k2_zfmisc_1(A_395,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2451,c_2393])).

tff(c_2559,plain,(
    ! [D_401,A_402] : ~ r2_hidden(D_401,k2_zfmisc_1(A_402,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_2466,c_2508])).

tff(c_2664,plain,(
    ! [D_408,B_409] : ~ r2_hidden(D_408,k2_zfmisc_1('#skF_8',B_409)) ),
    inference(resolution,[status(thm)],[c_2447,c_2559])).

tff(c_2702,plain,(
    ! [B_409] : k2_zfmisc_1('#skF_8',B_409) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2372,c_2664])).

tff(c_2341,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_46])).

tff(c_2342,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2341])).

tff(c_2349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2336,c_2342])).

tff(c_2350,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2358,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2336,c_2350])).

tff(c_2706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_2358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.61  
% 3.17/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.62  %$ r2_hidden > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 3.17/1.62  
% 3.17/1.62  %Foreground sorts:
% 3.17/1.62  
% 3.17/1.62  
% 3.17/1.62  %Background operators:
% 3.17/1.62  
% 3.17/1.62  
% 3.17/1.62  %Foreground operators:
% 3.17/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.62  tff('#skF_11', type, '#skF_11': $i).
% 3.17/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.17/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.17/1.62  tff('#skF_10', type, '#skF_10': $i).
% 3.17/1.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.17/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.17/1.62  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.17/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.17/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.17/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.62  
% 3.54/1.64  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.54/1.64  tff(f_61, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.54/1.64  tff(f_54, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.54/1.64  tff(f_42, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.54/1.64  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.54/1.64  tff(c_14, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.64  tff(c_44, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_63, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_44])).
% 3.54/1.64  tff(c_48, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_62, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_48])).
% 3.54/1.64  tff(c_52, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_66, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.54/1.64  tff(c_125, plain, (![E_59, F_60, A_61, B_62]: (r2_hidden(k4_tarski(E_59, F_60), k2_zfmisc_1(A_61, B_62)) | ~r2_hidden(F_60, B_62) | ~r2_hidden(E_59, A_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_129, plain, (![E_63, F_64]: (r2_hidden(k4_tarski(E_63, F_64), k1_xboole_0) | ~r2_hidden(F_64, '#skF_11') | ~r2_hidden(E_63, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_125])).
% 3.54/1.64  tff(c_16, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.54/1.64  tff(c_95, plain, (![A_51, B_52, C_53]: (r2_hidden(A_51, B_52) | ~r2_hidden(A_51, C_53) | r2_hidden(A_51, k5_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_104, plain, (![A_51, A_6]: (r2_hidden(A_51, A_6) | ~r2_hidden(A_51, k1_xboole_0) | r2_hidden(A_51, A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_95])).
% 3.54/1.64  tff(c_134, plain, (![E_63, F_64, A_6]: (r2_hidden(k4_tarski(E_63, F_64), A_6) | ~r2_hidden(F_64, '#skF_11') | ~r2_hidden(E_63, '#skF_10'))), inference(resolution, [status(thm)], [c_129, c_104])).
% 3.54/1.64  tff(c_80, plain, (![A_46, C_47, B_48]: (~r2_hidden(A_46, C_47) | ~r2_hidden(A_46, B_48) | ~r2_hidden(A_46, k5_xboole_0(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_87, plain, (![A_46, A_6]: (~r2_hidden(A_46, k1_xboole_0) | ~r2_hidden(A_46, A_6) | ~r2_hidden(A_46, A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_80])).
% 3.54/1.64  tff(c_155, plain, (![E_68, F_69, A_70]: (~r2_hidden(k4_tarski(E_68, F_69), A_70) | ~r2_hidden(F_69, '#skF_11') | ~r2_hidden(E_68, '#skF_10'))), inference(resolution, [status(thm)], [c_129, c_87])).
% 3.54/1.64  tff(c_170, plain, (![F_64, E_63]: (~r2_hidden(F_64, '#skF_11') | ~r2_hidden(E_63, '#skF_10'))), inference(resolution, [status(thm)], [c_134, c_155])).
% 3.54/1.64  tff(c_175, plain, (![E_71]: (~r2_hidden(E_71, '#skF_10'))), inference(splitLeft, [status(thm)], [c_170])).
% 3.54/1.64  tff(c_179, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_14, c_175])).
% 3.54/1.64  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_179])).
% 3.54/1.64  tff(c_185, plain, (![F_72]: (~r2_hidden(F_72, '#skF_11'))), inference(splitRight, [status(thm)], [c_170])).
% 3.54/1.64  tff(c_189, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_185])).
% 3.54/1.64  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_189])).
% 3.54/1.64  tff(c_194, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 3.54/1.64  tff(c_196, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_194])).
% 3.54/1.64  tff(c_199, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_14])).
% 3.54/1.64  tff(c_272, plain, (![A_95, B_96, D_97]: (r2_hidden('#skF_7'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97), B_96) | ~r2_hidden(D_97, k2_zfmisc_1(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_202, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_9')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_16])).
% 3.54/1.64  tff(c_240, plain, (![A_83, B_84, C_85]: (r2_hidden(A_83, B_84) | ~r2_hidden(A_83, C_85) | r2_hidden(A_83, k5_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_246, plain, (![A_83, A_6]: (r2_hidden(A_83, A_6) | ~r2_hidden(A_83, '#skF_9') | r2_hidden(A_83, A_6))), inference(superposition, [status(thm), theory('equality')], [c_202, c_240])).
% 3.54/1.64  tff(c_287, plain, (![A_95, D_97, A_6]: (r2_hidden('#skF_7'(A_95, '#skF_9', k2_zfmisc_1(A_95, '#skF_9'), D_97), A_6) | ~r2_hidden(D_97, k2_zfmisc_1(A_95, '#skF_9')))), inference(resolution, [status(thm)], [c_272, c_246])).
% 3.54/1.64  tff(c_217, plain, (![A_75, C_76, B_77]: (~r2_hidden(A_75, C_76) | ~r2_hidden(A_75, B_77) | ~r2_hidden(A_75, k5_xboole_0(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_224, plain, (![A_75, A_6]: (~r2_hidden(A_75, '#skF_9') | ~r2_hidden(A_75, A_6) | ~r2_hidden(A_75, A_6))), inference(superposition, [status(thm), theory('equality')], [c_202, c_217])).
% 3.54/1.64  tff(c_367, plain, (![A_110, D_111, A_112]: (~r2_hidden('#skF_7'(A_110, '#skF_9', k2_zfmisc_1(A_110, '#skF_9'), D_111), A_112) | ~r2_hidden(D_111, k2_zfmisc_1(A_110, '#skF_9')))), inference(resolution, [status(thm)], [c_272, c_224])).
% 3.54/1.64  tff(c_387, plain, (![D_113, A_114]: (~r2_hidden(D_113, k2_zfmisc_1(A_114, '#skF_9')))), inference(resolution, [status(thm)], [c_287, c_367])).
% 3.54/1.64  tff(c_416, plain, (![A_114]: (k2_zfmisc_1(A_114, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_199, c_387])).
% 3.54/1.64  tff(c_50, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_65, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.54/1.64  tff(c_198, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_65])).
% 3.54/1.64  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_198])).
% 3.54/1.64  tff(c_462, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_194])).
% 3.54/1.64  tff(c_467, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_14])).
% 3.54/1.64  tff(c_540, plain, (![A_140, B_141, D_142]: (r2_hidden('#skF_6'(A_140, B_141, k2_zfmisc_1(A_140, B_141), D_142), A_140) | ~r2_hidden(D_142, k2_zfmisc_1(A_140, B_141)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_470, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_8')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_462, c_16])).
% 3.54/1.64  tff(c_508, plain, (![A_128, B_129, C_130]: (r2_hidden(A_128, B_129) | ~r2_hidden(A_128, C_130) | r2_hidden(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_514, plain, (![A_128, A_6]: (r2_hidden(A_128, A_6) | ~r2_hidden(A_128, '#skF_8') | r2_hidden(A_128, A_6))), inference(superposition, [status(thm), theory('equality')], [c_470, c_508])).
% 3.54/1.64  tff(c_556, plain, (![B_141, D_142, A_6]: (r2_hidden('#skF_6'('#skF_8', B_141, k2_zfmisc_1('#skF_8', B_141), D_142), A_6) | ~r2_hidden(D_142, k2_zfmisc_1('#skF_8', B_141)))), inference(resolution, [status(thm)], [c_540, c_514])).
% 3.54/1.64  tff(c_489, plain, (![A_123, C_124, B_125]: (~r2_hidden(A_123, C_124) | ~r2_hidden(A_123, B_125) | ~r2_hidden(A_123, k5_xboole_0(B_125, C_124)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_499, plain, (![A_123, A_6]: (~r2_hidden(A_123, '#skF_8') | ~r2_hidden(A_123, A_6) | ~r2_hidden(A_123, A_6))), inference(superposition, [status(thm), theory('equality')], [c_470, c_489])).
% 3.54/1.64  tff(c_628, plain, (![B_152, D_153, A_154]: (~r2_hidden('#skF_6'('#skF_8', B_152, k2_zfmisc_1('#skF_8', B_152), D_153), A_154) | ~r2_hidden(D_153, k2_zfmisc_1('#skF_8', B_152)))), inference(resolution, [status(thm)], [c_540, c_499])).
% 3.54/1.64  tff(c_648, plain, (![D_155, B_156]: (~r2_hidden(D_155, k2_zfmisc_1('#skF_8', B_156)))), inference(resolution, [status(thm)], [c_556, c_628])).
% 3.54/1.64  tff(c_678, plain, (![B_156]: (k2_zfmisc_1('#skF_8', B_156)='#skF_8')), inference(resolution, [status(thm)], [c_467, c_648])).
% 3.54/1.64  tff(c_466, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_462, c_65])).
% 3.54/1.64  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_678, c_466])).
% 3.54/1.64  tff(c_684, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.64  tff(c_748, plain, (![E_173, F_174, A_175, B_176]: (r2_hidden(k4_tarski(E_173, F_174), k2_zfmisc_1(A_175, B_176)) | ~r2_hidden(F_174, B_176) | ~r2_hidden(E_173, A_175))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_751, plain, (![E_173, F_174]: (r2_hidden(k4_tarski(E_173, F_174), k1_xboole_0) | ~r2_hidden(F_174, '#skF_9') | ~r2_hidden(E_173, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_684, c_748])).
% 3.54/1.64  tff(c_755, plain, (![E_177, F_178]: (r2_hidden(k4_tarski(E_177, F_178), k1_xboole_0) | ~r2_hidden(F_178, '#skF_9') | ~r2_hidden(E_177, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_684, c_748])).
% 3.54/1.64  tff(c_725, plain, (![A_168, C_169, B_170]: (~r2_hidden(A_168, C_169) | ~r2_hidden(A_168, B_170) | ~r2_hidden(A_168, k5_xboole_0(B_170, C_169)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_738, plain, (![A_168, A_6]: (~r2_hidden(A_168, k1_xboole_0) | ~r2_hidden(A_168, A_6) | ~r2_hidden(A_168, A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_725])).
% 3.54/1.64  tff(c_798, plain, (![E_186, F_187, A_188]: (~r2_hidden(k4_tarski(E_186, F_187), A_188) | ~r2_hidden(F_187, '#skF_9') | ~r2_hidden(E_186, '#skF_8'))), inference(resolution, [status(thm)], [c_755, c_738])).
% 3.54/1.64  tff(c_817, plain, (![F_174, E_173]: (~r2_hidden(F_174, '#skF_9') | ~r2_hidden(E_173, '#skF_8'))), inference(resolution, [status(thm)], [c_751, c_798])).
% 3.54/1.64  tff(c_823, plain, (![E_189]: (~r2_hidden(E_189, '#skF_8'))), inference(splitLeft, [status(thm)], [c_817])).
% 3.54/1.64  tff(c_833, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_14, c_823])).
% 3.54/1.64  tff(c_841, plain, ('#skF_11'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_63])).
% 3.54/1.64  tff(c_840, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_14])).
% 3.54/1.64  tff(c_842, plain, ('#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_62])).
% 3.54/1.64  tff(c_821, plain, (![E_173]: (~r2_hidden(E_173, '#skF_8'))), inference(splitLeft, [status(thm)], [c_817])).
% 3.54/1.64  tff(c_683, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.64  tff(c_754, plain, (![E_173, F_174]: (r2_hidden(k4_tarski(E_173, F_174), k1_xboole_0) | ~r2_hidden(F_174, '#skF_11') | ~r2_hidden(E_173, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_683, c_748])).
% 3.54/1.64  tff(c_834, plain, (![E_173, F_174]: (r2_hidden(k4_tarski(E_173, F_174), '#skF_8') | ~r2_hidden(F_174, '#skF_11') | ~r2_hidden(E_173, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_754])).
% 3.54/1.64  tff(c_844, plain, (![F_174, E_173]: (~r2_hidden(F_174, '#skF_11') | ~r2_hidden(E_173, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_821, c_834])).
% 3.54/1.64  tff(c_1066, plain, (![E_204]: (~r2_hidden(E_204, '#skF_10'))), inference(splitLeft, [status(thm)], [c_844])).
% 3.54/1.64  tff(c_1076, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_840, c_1066])).
% 3.54/1.64  tff(c_1089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_842, c_1076])).
% 3.54/1.64  tff(c_1091, plain, (![F_205]: (~r2_hidden(F_205, '#skF_11'))), inference(splitRight, [status(thm)], [c_844])).
% 3.54/1.64  tff(c_1101, plain, ('#skF_11'='#skF_8'), inference(resolution, [status(thm)], [c_840, c_1091])).
% 3.54/1.64  tff(c_1114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_841, c_1101])).
% 3.54/1.64  tff(c_1139, plain, (![F_209]: (~r2_hidden(F_209, '#skF_9'))), inference(splitRight, [status(thm)], [c_817])).
% 3.54/1.64  tff(c_1149, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_14, c_1139])).
% 3.54/1.64  tff(c_1158, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_63])).
% 3.54/1.64  tff(c_1501, plain, (![A_235]: (r2_hidden('#skF_1'(A_235), A_235) | A_235='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_14])).
% 3.54/1.64  tff(c_1159, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_62])).
% 3.54/1.64  tff(c_1416, plain, (![A_229]: (r2_hidden('#skF_1'(A_229), A_229) | A_229='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_14])).
% 3.54/1.64  tff(c_1115, plain, (![F_174]: (~r2_hidden(F_174, '#skF_9'))), inference(splitRight, [status(thm)], [c_817])).
% 3.54/1.64  tff(c_1150, plain, (![E_173, F_174]: (r2_hidden(k4_tarski(E_173, F_174), '#skF_9') | ~r2_hidden(F_174, '#skF_11') | ~r2_hidden(E_173, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_754])).
% 3.54/1.64  tff(c_1161, plain, (![F_174, E_173]: (~r2_hidden(F_174, '#skF_11') | ~r2_hidden(E_173, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_1115, c_1150])).
% 3.54/1.64  tff(c_1295, plain, (![E_173]: (~r2_hidden(E_173, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1161])).
% 3.54/1.64  tff(c_1428, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_1416, c_1295])).
% 3.54/1.64  tff(c_1454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1159, c_1428])).
% 3.54/1.64  tff(c_1455, plain, (![F_174]: (~r2_hidden(F_174, '#skF_11'))), inference(splitRight, [status(thm)], [c_1161])).
% 3.54/1.64  tff(c_1513, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_1501, c_1455])).
% 3.54/1.64  tff(c_1539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1158, c_1513])).
% 3.54/1.64  tff(c_1541, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_44])).
% 3.54/1.64  tff(c_1540, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 3.54/1.64  tff(c_1557, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1541, c_1540])).
% 3.54/1.64  tff(c_1558, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_1557])).
% 3.54/1.64  tff(c_1561, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1541])).
% 3.54/1.64  tff(c_1586, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_14])).
% 3.54/1.64  tff(c_22, plain, (![A_7, B_8, D_34]: (r2_hidden('#skF_7'(A_7, B_8, k2_zfmisc_1(A_7, B_8), D_34), B_8) | ~r2_hidden(D_34, k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_1645, plain, (![A_259, B_260, D_261]: (r2_hidden('#skF_6'(A_259, B_260, k2_zfmisc_1(A_259, B_260), D_261), A_259) | ~r2_hidden(D_261, k2_zfmisc_1(A_259, B_260)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_1543, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_11')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_16])).
% 3.54/1.64  tff(c_1559, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_9')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1543])).
% 3.54/1.64  tff(c_1613, plain, (![A_247, B_248, C_249]: (r2_hidden(A_247, B_248) | ~r2_hidden(A_247, C_249) | r2_hidden(A_247, k5_xboole_0(B_248, C_249)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_1619, plain, (![A_247, A_6]: (r2_hidden(A_247, A_6) | ~r2_hidden(A_247, '#skF_9') | r2_hidden(A_247, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_1613])).
% 3.54/1.64  tff(c_1661, plain, (![B_260, D_261, A_6]: (r2_hidden('#skF_6'('#skF_9', B_260, k2_zfmisc_1('#skF_9', B_260), D_261), A_6) | ~r2_hidden(D_261, k2_zfmisc_1('#skF_9', B_260)))), inference(resolution, [status(thm)], [c_1645, c_1619])).
% 3.54/1.64  tff(c_1590, plain, (![A_239, C_240, B_241]: (~r2_hidden(A_239, C_240) | ~r2_hidden(A_239, B_241) | ~r2_hidden(A_239, k5_xboole_0(B_241, C_240)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_1597, plain, (![A_239, A_6]: (~r2_hidden(A_239, '#skF_9') | ~r2_hidden(A_239, A_6) | ~r2_hidden(A_239, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_1590])).
% 3.54/1.64  tff(c_1733, plain, (![B_271, D_272, A_273]: (~r2_hidden('#skF_6'('#skF_9', B_271, k2_zfmisc_1('#skF_9', B_271), D_272), A_273) | ~r2_hidden(D_272, k2_zfmisc_1('#skF_9', B_271)))), inference(resolution, [status(thm)], [c_1645, c_1597])).
% 3.54/1.64  tff(c_1753, plain, (![D_274, B_275]: (~r2_hidden(D_274, k2_zfmisc_1('#skF_9', B_275)))), inference(resolution, [status(thm)], [c_1661, c_1733])).
% 3.54/1.64  tff(c_1783, plain, (![B_275]: (k2_zfmisc_1('#skF_9', B_275)='#skF_9')), inference(resolution, [status(thm)], [c_1586, c_1753])).
% 3.54/1.64  tff(c_1749, plain, (![D_261, B_260]: (~r2_hidden(D_261, k2_zfmisc_1('#skF_9', B_260)))), inference(resolution, [status(thm)], [c_1661, c_1733])).
% 3.54/1.64  tff(c_1803, plain, (![D_277]: (~r2_hidden(D_277, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1749])).
% 3.54/1.64  tff(c_1845, plain, (![D_281, A_282]: (~r2_hidden(D_281, k2_zfmisc_1(A_282, '#skF_9')))), inference(resolution, [status(thm)], [c_22, c_1803])).
% 3.54/1.64  tff(c_1883, plain, (![A_282]: (k2_zfmisc_1(A_282, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_1586, c_1845])).
% 3.54/1.64  tff(c_42, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_1566, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_42])).
% 3.54/1.64  tff(c_1567, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_1566])).
% 3.54/1.64  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1567, c_1561])).
% 3.54/1.64  tff(c_1569, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1566])).
% 3.54/1.64  tff(c_1585, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_1569])).
% 3.54/1.64  tff(c_1887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1585])).
% 3.54/1.64  tff(c_1888, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_1557])).
% 3.54/1.64  tff(c_1895, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1541])).
% 3.54/1.64  tff(c_1914, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_14])).
% 3.54/1.64  tff(c_1974, plain, (![A_305, B_306, D_307]: (r2_hidden('#skF_6'(A_305, B_306, k2_zfmisc_1(A_305, B_306), D_307), A_305) | ~r2_hidden(D_307, k2_zfmisc_1(A_305, B_306)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_1893, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_8')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1543])).
% 3.54/1.64  tff(c_1943, plain, (![A_293, B_294, C_295]: (r2_hidden(A_293, B_294) | ~r2_hidden(A_293, C_295) | r2_hidden(A_293, k5_xboole_0(B_294, C_295)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_1952, plain, (![A_293, A_6]: (r2_hidden(A_293, A_6) | ~r2_hidden(A_293, '#skF_8') | r2_hidden(A_293, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_1943])).
% 3.54/1.64  tff(c_1989, plain, (![B_306, D_307, A_6]: (r2_hidden('#skF_6'('#skF_8', B_306, k2_zfmisc_1('#skF_8', B_306), D_307), A_6) | ~r2_hidden(D_307, k2_zfmisc_1('#skF_8', B_306)))), inference(resolution, [status(thm)], [c_1974, c_1952])).
% 3.54/1.64  tff(c_1928, plain, (![A_288, C_289, B_290]: (~r2_hidden(A_288, C_289) | ~r2_hidden(A_288, B_290) | ~r2_hidden(A_288, k5_xboole_0(B_290, C_289)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_1935, plain, (![A_288, A_6]: (~r2_hidden(A_288, '#skF_8') | ~r2_hidden(A_288, A_6) | ~r2_hidden(A_288, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_1928])).
% 3.54/1.64  tff(c_2081, plain, (![B_320, D_321, A_322]: (~r2_hidden('#skF_6'('#skF_8', B_320, k2_zfmisc_1('#skF_8', B_320), D_321), A_322) | ~r2_hidden(D_321, k2_zfmisc_1('#skF_8', B_320)))), inference(resolution, [status(thm)], [c_1974, c_1935])).
% 3.54/1.64  tff(c_2101, plain, (![D_323, B_324]: (~r2_hidden(D_323, k2_zfmisc_1('#skF_8', B_324)))), inference(resolution, [status(thm)], [c_1989, c_2081])).
% 3.54/1.64  tff(c_2135, plain, (![B_324]: (k2_zfmisc_1('#skF_8', B_324)='#skF_8')), inference(resolution, [status(thm)], [c_1914, c_2101])).
% 3.54/1.64  tff(c_1891, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1541, c_42])).
% 3.54/1.64  tff(c_1892, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1891])).
% 3.54/1.64  tff(c_2139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2135, c_1892])).
% 3.54/1.64  tff(c_2141, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 3.54/1.64  tff(c_2140, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_48])).
% 3.54/1.64  tff(c_2147, plain, ('#skF_10'='#skF_8' | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2141, c_2141, c_2140])).
% 3.54/1.64  tff(c_2148, plain, ('#skF_10'='#skF_9'), inference(splitLeft, [status(thm)], [c_2147])).
% 3.54/1.64  tff(c_2149, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2148, c_2141])).
% 3.54/1.64  tff(c_2171, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_14])).
% 3.54/1.64  tff(c_2231, plain, (![A_347, B_348, D_349]: (r2_hidden('#skF_7'(A_347, B_348, k2_zfmisc_1(A_347, B_348), D_349), B_348) | ~r2_hidden(D_349, k2_zfmisc_1(A_347, B_348)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_2142, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_10')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2141, c_16])).
% 3.54/1.64  tff(c_2158, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_9')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2148, c_2142])).
% 3.54/1.64  tff(c_2207, plain, (![A_338, C_339, B_340]: (~r2_hidden(A_338, C_339) | ~r2_hidden(A_338, B_340) | ~r2_hidden(A_338, k5_xboole_0(B_340, C_339)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_2220, plain, (![A_338, A_6]: (~r2_hidden(A_338, '#skF_9') | ~r2_hidden(A_338, A_6) | ~r2_hidden(A_338, A_6))), inference(superposition, [status(thm), theory('equality')], [c_2158, c_2207])).
% 3.54/1.64  tff(c_2269, plain, (![A_353, D_354, A_355]: (~r2_hidden('#skF_7'(A_353, '#skF_9', k2_zfmisc_1(A_353, '#skF_9'), D_354), A_355) | ~r2_hidden(D_354, k2_zfmisc_1(A_353, '#skF_9')))), inference(resolution, [status(thm)], [c_2231, c_2220])).
% 3.54/1.64  tff(c_2304, plain, (![D_359, A_360]: (~r2_hidden(D_359, k2_zfmisc_1(A_360, '#skF_9')))), inference(resolution, [status(thm)], [c_22, c_2269])).
% 3.54/1.64  tff(c_2329, plain, (![A_360]: (k2_zfmisc_1(A_360, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_2171, c_2304])).
% 3.54/1.64  tff(c_46, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.64  tff(c_2169, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_2148, c_2149, c_46])).
% 3.54/1.64  tff(c_2333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2169])).
% 3.54/1.64  tff(c_2334, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_2147])).
% 3.54/1.64  tff(c_2336, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2141])).
% 3.54/1.64  tff(c_2372, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2336, c_14])).
% 3.54/1.64  tff(c_2432, plain, (![A_383, B_384, D_385]: (r2_hidden('#skF_6'(A_383, B_384, k2_zfmisc_1(A_383, B_384), D_385), A_383) | ~r2_hidden(D_385, k2_zfmisc_1(A_383, B_384)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_2359, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_8')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2142])).
% 3.54/1.64  tff(c_2395, plain, (![A_369, B_370, C_371]: (r2_hidden(A_369, B_370) | ~r2_hidden(A_369, C_371) | r2_hidden(A_369, k5_xboole_0(B_370, C_371)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_2404, plain, (![A_369, A_6]: (r2_hidden(A_369, A_6) | ~r2_hidden(A_369, '#skF_8') | r2_hidden(A_369, A_6))), inference(superposition, [status(thm), theory('equality')], [c_2359, c_2395])).
% 3.54/1.64  tff(c_2447, plain, (![B_384, D_385, A_6]: (r2_hidden('#skF_6'('#skF_8', B_384, k2_zfmisc_1('#skF_8', B_384), D_385), A_6) | ~r2_hidden(D_385, k2_zfmisc_1('#skF_8', B_384)))), inference(resolution, [status(thm)], [c_2432, c_2404])).
% 3.54/1.64  tff(c_2451, plain, (![A_386, B_387, D_388]: (r2_hidden('#skF_7'(A_386, B_387, k2_zfmisc_1(A_386, B_387), D_388), B_387) | ~r2_hidden(D_388, k2_zfmisc_1(A_386, B_387)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.64  tff(c_2466, plain, (![A_386, D_388, A_6]: (r2_hidden('#skF_7'(A_386, '#skF_8', k2_zfmisc_1(A_386, '#skF_8'), D_388), A_6) | ~r2_hidden(D_388, k2_zfmisc_1(A_386, '#skF_8')))), inference(resolution, [status(thm)], [c_2451, c_2404])).
% 3.54/1.64  tff(c_2386, plain, (![A_366, C_367, B_368]: (~r2_hidden(A_366, C_367) | ~r2_hidden(A_366, B_368) | ~r2_hidden(A_366, k5_xboole_0(B_368, C_367)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.64  tff(c_2393, plain, (![A_366, A_6]: (~r2_hidden(A_366, '#skF_8') | ~r2_hidden(A_366, A_6) | ~r2_hidden(A_366, A_6))), inference(superposition, [status(thm), theory('equality')], [c_2359, c_2386])).
% 3.54/1.64  tff(c_2508, plain, (![A_395, D_396, A_397]: (~r2_hidden('#skF_7'(A_395, '#skF_8', k2_zfmisc_1(A_395, '#skF_8'), D_396), A_397) | ~r2_hidden(D_396, k2_zfmisc_1(A_395, '#skF_8')))), inference(resolution, [status(thm)], [c_2451, c_2393])).
% 3.54/1.64  tff(c_2559, plain, (![D_401, A_402]: (~r2_hidden(D_401, k2_zfmisc_1(A_402, '#skF_8')))), inference(resolution, [status(thm)], [c_2466, c_2508])).
% 3.54/1.64  tff(c_2664, plain, (![D_408, B_409]: (~r2_hidden(D_408, k2_zfmisc_1('#skF_8', B_409)))), inference(resolution, [status(thm)], [c_2447, c_2559])).
% 3.54/1.64  tff(c_2702, plain, (![B_409]: (k2_zfmisc_1('#skF_8', B_409)='#skF_8')), inference(resolution, [status(thm)], [c_2372, c_2664])).
% 3.54/1.64  tff(c_2341, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_46])).
% 3.54/1.64  tff(c_2342, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_2341])).
% 3.54/1.64  tff(c_2349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2336, c_2342])).
% 3.54/1.64  tff(c_2350, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2341])).
% 3.54/1.64  tff(c_2358, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2336, c_2350])).
% 3.54/1.64  tff(c_2706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2702, c_2358])).
% 3.54/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.64  
% 3.54/1.64  Inference rules
% 3.54/1.64  ----------------------
% 3.54/1.64  #Ref     : 0
% 3.54/1.64  #Sup     : 545
% 3.54/1.64  #Fact    : 0
% 3.54/1.64  #Define  : 0
% 3.54/1.64  #Split   : 13
% 3.54/1.64  #Chain   : 0
% 3.54/1.64  #Close   : 0
% 3.54/1.64  
% 3.54/1.64  Ordering : KBO
% 3.54/1.64  
% 3.54/1.64  Simplification rules
% 3.54/1.64  ----------------------
% 3.54/1.64  #Subsume      : 137
% 3.54/1.64  #Demod        : 154
% 3.54/1.64  #Tautology    : 157
% 3.54/1.64  #SimpNegUnit  : 27
% 3.54/1.64  #BackRed      : 63
% 3.54/1.64  
% 3.54/1.64  #Partial instantiations: 0
% 3.54/1.64  #Strategies tried      : 1
% 3.54/1.64  
% 3.54/1.64  Timing (in seconds)
% 3.54/1.64  ----------------------
% 3.54/1.65  Preprocessing        : 0.29
% 3.54/1.65  Parsing              : 0.14
% 3.54/1.65  CNF conversion       : 0.02
% 3.54/1.65  Main loop            : 0.53
% 3.54/1.65  Inferencing          : 0.22
% 3.54/1.65  Reduction            : 0.13
% 3.54/1.65  Demodulation         : 0.08
% 3.54/1.65  BG Simplification    : 0.03
% 3.54/1.65  Subsumption          : 0.10
% 3.54/1.65  Abstraction          : 0.03
% 3.54/1.65  MUC search           : 0.00
% 3.54/1.65  Cooper               : 0.00
% 3.54/1.65  Total                : 0.89
% 3.54/1.65  Index Insertion      : 0.00
% 3.54/1.65  Index Deletion       : 0.00
% 3.54/1.65  Index Matching       : 0.00
% 3.54/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
