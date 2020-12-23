%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 18.14s
% Output     : CNFRefutation 18.56s
% Verified   : 
% Statistics : Number of formulae       :  365 (9157 expanded)
%              Number of leaves         :   35 (3024 expanded)
%              Depth                    :   19
%              Number of atoms          :  523 (18590 expanded)
%              Number of equality atoms :  231 (11131 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_82,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_99,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_99])).

tff(c_492,plain,(
    ! [B_124,A_125] :
      ( k1_tarski(B_124) = A_125
      | k1_xboole_0 = A_125
      | ~ r1_tarski(A_125,k1_tarski(B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_498,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_102,c_492])).

tff(c_506,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_498])).

tff(c_513,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_84])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_271,plain,(
    ! [A_92,C_93,B_94] :
      ( r2_hidden(A_92,C_93)
      | ~ r1_tarski(k2_tarski(A_92,B_94),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_282,plain,(
    ! [A_20,C_93] :
      ( r2_hidden(A_20,C_93)
      | ~ r1_tarski(k1_tarski(A_20),C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_271])).

tff(c_528,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_6',C_93)
      | ~ r1_tarski('#skF_7',C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_282])).

tff(c_68,plain,(
    ! [B_49] : r1_tarski(k1_xboole_0,k1_tarski(B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_140,plain,(
    ! [A_73,B_74] :
      ( k2_xboole_0(A_73,B_74) = B_74
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    ! [B_49] : k2_xboole_0(k1_xboole_0,k1_tarski(B_49)) = k1_tarski(B_49) ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_350,plain,(
    ! [D_110,A_111,B_112] :
      ( ~ r2_hidden(D_110,A_111)
      | r2_hidden(D_110,k2_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_359,plain,(
    ! [D_110,B_49] :
      ( ~ r2_hidden(D_110,k1_xboole_0)
      | r2_hidden(D_110,k1_tarski(B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_350])).

tff(c_813,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_tarski(k2_tarski(A_137,B_138),C_139)
      | ~ r2_hidden(B_138,C_139)
      | ~ r2_hidden(A_137,C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1021,plain,(
    ! [A_148,C_149] :
      ( r1_tarski(k1_tarski(A_148),C_149)
      | ~ r2_hidden(A_148,C_149)
      | ~ r2_hidden(A_148,C_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_813])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1043,plain,(
    ! [A_150,C_151] :
      ( k2_xboole_0(k1_tarski(A_150),C_151) = C_151
      | ~ r2_hidden(A_150,C_151) ) ),
    inference(resolution,[status(thm)],[c_1021,c_22])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1155,plain,(
    ! [A_152,C_153] :
      ( r1_tarski(k1_tarski(A_152),C_153)
      | ~ r2_hidden(A_152,C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_24])).

tff(c_1177,plain,(
    ! [C_154] :
      ( r1_tarski('#skF_7',C_154)
      | ~ r2_hidden('#skF_6',C_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_1155])).

tff(c_1264,plain,(
    ! [B_49] :
      ( r1_tarski('#skF_7',k1_tarski(B_49))
      | ~ r2_hidden('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_359,c_1177])).

tff(c_49067,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1264])).

tff(c_49079,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_528,c_49067])).

tff(c_327,plain,(
    ! [D_104,B_105,A_106] :
      ( ~ r2_hidden(D_104,B_105)
      | r2_hidden(D_104,k2_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_342,plain,(
    ! [D_104] :
      ( ~ r2_hidden(D_104,'#skF_8')
      | r2_hidden(D_104,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_327])).

tff(c_510,plain,(
    ! [D_104] :
      ( ~ r2_hidden(D_104,'#skF_8')
      | r2_hidden(D_104,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_342])).

tff(c_64,plain,(
    ! [B_49,A_48] :
      ( k1_tarski(B_49) = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k1_tarski(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_517,plain,(
    ! [A_48] :
      ( k1_tarski('#skF_6') = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_64])).

tff(c_563,plain,(
    ! [A_48] :
      ( A_48 = '#skF_7'
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_517])).

tff(c_49647,plain,(
    ! [A_223704] :
      ( k1_tarski(A_223704) = '#skF_7'
      | k1_tarski(A_223704) = k1_xboole_0
      | ~ r2_hidden(A_223704,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1021,c_563])).

tff(c_69100,plain,(
    ! [D_309147] :
      ( k1_tarski(D_309147) = '#skF_7'
      | k1_tarski(D_309147) = k1_xboole_0
      | ~ r2_hidden(D_309147,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_510,c_49647])).

tff(c_69112,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_69100])).

tff(c_69121,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_69112])).

tff(c_69122,plain,(
    k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69121])).

tff(c_187,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [E_19,B_14,C_15] : r2_hidden(E_19,k1_enumset1(E_19,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_32])).

tff(c_208,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_205])).

tff(c_69164,plain,(
    r2_hidden('#skF_3'('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69122,c_208])).

tff(c_525,plain,(
    ! [D_110] :
      ( ~ r2_hidden(D_110,k1_xboole_0)
      | r2_hidden(D_110,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_359])).

tff(c_69289,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_69164,c_525])).

tff(c_28,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [B_78,A_77] : r2_hidden(B_78,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_28])).

tff(c_1339,plain,(
    ! [C_168] :
      ( k2_xboole_0('#skF_7',C_168) = C_168
      | ~ r2_hidden('#skF_6',C_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_1043])).

tff(c_49333,plain,(
    ! [A_223691] : k2_xboole_0('#skF_7',k2_tarski(A_223691,'#skF_6')) = k2_tarski(A_223691,'#skF_6') ),
    inference(resolution,[status(thm)],[c_196,c_1339])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_49351,plain,(
    ! [D_6,A_223691] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,k2_tarski(A_223691,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49333,c_6])).

tff(c_1042,plain,(
    ! [A_148,C_149] :
      ( k2_xboole_0(k1_tarski(A_148),C_149) = C_149
      | ~ r2_hidden(A_148,C_149) ) ),
    inference(resolution,[status(thm)],[c_1021,c_22])).

tff(c_70480,plain,(
    ! [C_309185] :
      ( k2_xboole_0(k1_xboole_0,C_309185) = C_309185
      | ~ r2_hidden('#skF_3'('#skF_8'),C_309185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69122,c_1042])).

tff(c_70520,plain,(
    ! [A_223691] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski(A_223691,'#skF_6')) = k2_tarski(A_223691,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_49351,c_70480])).

tff(c_86940,plain,(
    ! [A_394489] : k2_xboole_0(k1_xboole_0,k2_tarski(A_394489,'#skF_6')) = k2_tarski(A_394489,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69289,c_70520])).

tff(c_235,plain,(
    ! [B_85,C_86,A_87] :
      ( r2_hidden(B_85,C_86)
      | ~ r1_tarski(k2_tarski(A_87,B_85),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_263,plain,(
    ! [B_89,A_90,B_91] : r2_hidden(B_89,k2_xboole_0(k2_tarski(A_90,B_89),B_91)) ),
    inference(resolution,[status(thm)],[c_24,c_235])).

tff(c_270,plain,(
    ! [A_20,B_91] : r2_hidden(A_20,k2_xboole_0(k1_tarski(A_20),B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_263])).

tff(c_69152,plain,(
    ! [B_91] : r2_hidden('#skF_3'('#skF_8'),k2_xboole_0(k1_xboole_0,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69122,c_270])).

tff(c_86945,plain,(
    ! [A_394489] : r2_hidden('#skF_3'('#skF_8'),k2_tarski(A_394489,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86940,c_69152])).

tff(c_52,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_992,plain,(
    ! [E_144,C_145,B_146,A_147] :
      ( E_144 = C_145
      | E_144 = B_146
      | E_144 = A_147
      | ~ r2_hidden(E_144,k1_enumset1(A_147,B_146,C_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_87007,plain,(
    ! [E_394815,B_394816,A_394817] :
      ( E_394815 = B_394816
      | E_394815 = A_394817
      | E_394815 = A_394817
      | ~ r2_hidden(E_394815,k2_tarski(A_394817,B_394816)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_87083,plain,(
    ! [A_394489] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | A_394489 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_86945,c_87007])).

tff(c_87183,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_87083])).

tff(c_87214,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87183,c_69164])).

tff(c_87230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49067,c_87214])).

tff(c_87480,plain,(
    '#skF_3'('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_87083])).

tff(c_108,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_117,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_108])).

tff(c_339,plain,(
    ! [D_104,A_20] :
      ( ~ r2_hidden(D_104,A_20)
      | r2_hidden(D_104,k3_tarski(k1_tarski(A_20))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_327])).

tff(c_523,plain,(
    ! [D_104] :
      ( ~ r2_hidden(D_104,'#skF_6')
      | r2_hidden(D_104,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_339])).

tff(c_1255,plain,
    ( r1_tarski('#skF_7',k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_523,c_1177])).

tff(c_1516,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_552,plain,(
    k2_xboole_0('#skF_6','#skF_6') = k3_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_117])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35964,plain,(
    ! [D_160324] :
      ( r2_hidden(D_160324,'#skF_6')
      | r2_hidden(D_160324,'#skF_6')
      | ~ r2_hidden(D_160324,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_2])).

tff(c_36010,plain,
    ( r2_hidden('#skF_6','#skF_6')
    | ~ r1_tarski('#skF_7',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_528,c_35964])).

tff(c_36032,plain,(
    ~ r1_tarski('#skF_7',k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1516,c_1516,c_36010])).

tff(c_1884,plain,(
    ! [A_198] :
      ( k1_tarski(A_198) = '#skF_7'
      | k1_tarski(A_198) = k1_xboole_0
      | ~ r2_hidden(A_198,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1155,c_563])).

tff(c_24643,plain,(
    ! [D_109359] :
      ( k1_tarski(D_109359) = '#skF_7'
      | k1_tarski(D_109359) = k1_xboole_0
      | ~ r2_hidden(D_109359,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_510,c_1884])).

tff(c_24655,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_24643])).

tff(c_24664,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_24655])).

tff(c_24665,plain,(
    k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24664])).

tff(c_1092,plain,(
    ! [A_150,C_151] :
      ( r1_tarski(k1_tarski(A_150),C_151)
      | ~ r2_hidden(A_150,C_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_24])).

tff(c_25090,plain,(
    ! [C_109372] :
      ( r1_tarski(k1_xboole_0,C_109372)
      | ~ r2_hidden('#skF_3'('#skF_8'),C_109372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_1092])).

tff(c_25206,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_523,c_25090])).

tff(c_25901,plain,(
    ~ r2_hidden('#skF_3'('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_25206])).

tff(c_24692,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_3'('#skF_8'),C_93)
      | ~ r1_tarski(k1_xboole_0,C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_282])).

tff(c_1898,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_1884])).

tff(c_1909,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1898])).

tff(c_1910,plain,(
    k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1909])).

tff(c_1952,plain,(
    r2_hidden('#skF_3'('#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_208])).

tff(c_2055,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1952,c_525])).

tff(c_193,plain,(
    ! [A_77,B_78] : r2_hidden(A_77,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_32])).

tff(c_1545,plain,(
    ! [B_181] : k2_xboole_0('#skF_7',k2_tarski('#skF_6',B_181)) = k2_tarski('#skF_6',B_181) ),
    inference(resolution,[status(thm)],[c_193,c_1339])).

tff(c_1559,plain,(
    ! [D_6,B_181] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,k2_tarski('#skF_6',B_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_6])).

tff(c_2441,plain,(
    ! [C_225] :
      ( k2_xboole_0(k1_xboole_0,C_225) = C_225
      | ~ r2_hidden('#skF_3'('#skF_7'),C_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_1042])).

tff(c_2460,plain,(
    ! [B_181] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski('#skF_6',B_181)) = k2_tarski('#skF_6',B_181)
      | ~ r2_hidden('#skF_3'('#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1559,c_2441])).

tff(c_12297,plain,(
    ! [B_50242] : k2_xboole_0(k1_xboole_0,k2_tarski('#skF_6',B_50242)) = k2_tarski('#skF_6',B_50242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2055,c_2460])).

tff(c_1940,plain,(
    ! [B_91] : r2_hidden('#skF_3'('#skF_7'),k2_xboole_0(k1_xboole_0,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_270])).

tff(c_12306,plain,(
    ! [B_50242] : r2_hidden('#skF_3'('#skF_7'),k2_tarski('#skF_6',B_50242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12297,c_1940])).

tff(c_22741,plain,(
    ! [E_98890,B_98891,A_98892] :
      ( E_98890 = B_98891
      | E_98890 = A_98892
      | E_98890 = A_98892
      | ~ r2_hidden(E_98890,k2_tarski(A_98892,B_98891)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_22839,plain,(
    ! [B_50242] :
      ( B_50242 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_12306,c_22741])).

tff(c_22850,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22839])).

tff(c_2144,plain,(
    ! [C_211] :
      ( r1_tarski(k1_xboole_0,C_211)
      | ~ r2_hidden('#skF_3'('#skF_7'),C_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_1092])).

tff(c_2251,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_523,c_2144])).

tff(c_2729,plain,(
    ~ r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2251])).

tff(c_1521,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1264])).

tff(c_9119,plain,(
    ! [A_28720,B_28721] : k2_xboole_0('#skF_7',k1_enumset1(A_28720,B_28721,'#skF_6')) = k1_enumset1(A_28720,B_28721,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_1339])).

tff(c_9439,plain,(
    ! [D_28884,A_28885,B_28886] :
      ( ~ r2_hidden(D_28884,'#skF_7')
      | r2_hidden(D_28884,k1_enumset1(A_28885,B_28886,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9119,c_6])).

tff(c_26,plain,(
    ! [E_19,C_15,B_14,A_13] :
      ( E_19 = C_15
      | E_19 = B_14
      | E_19 = A_13
      | ~ r2_hidden(E_19,k1_enumset1(A_13,B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9966,plain,(
    ! [D_29213,B_29214,A_29215] :
      ( D_29213 = '#skF_6'
      | D_29213 = B_29214
      | D_29213 = A_29215
      | ~ r2_hidden(D_29213,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9439,c_26])).

tff(c_10005,plain,(
    ! [B_29214,A_29215] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_29214 = '#skF_3'('#skF_7')
      | A_29215 = '#skF_3'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_9966])).

tff(c_10029,plain,(
    ! [B_29214,A_29215] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_29214 = '#skF_3'('#skF_7')
      | A_29215 = '#skF_3'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10005])).

tff(c_10194,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10029])).

tff(c_10219,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10194,c_1952])).

tff(c_10228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1521,c_10219])).

tff(c_10229,plain,(
    ! [A_29215,B_29214] :
      ( A_29215 = '#skF_3'('#skF_7')
      | B_29214 = '#skF_3'('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_10029])).

tff(c_10269,plain,(
    ! [B_30033] : B_30033 = '#skF_3'('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10229])).

tff(c_66,plain,(
    ! [B_49] : r1_tarski(k1_tarski(B_49),k1_tarski(B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1964,plain,(
    r1_tarski(k1_tarski('#skF_3'('#skF_7')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_66])).

tff(c_1977,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1964])).

tff(c_7316,plain,(
    ! [D_18617] :
      ( r2_hidden(D_18617,'#skF_6')
      | r2_hidden(D_18617,'#skF_6')
      | ~ r2_hidden(D_18617,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_2])).

tff(c_7381,plain,
    ( r2_hidden('#skF_3'(k3_tarski('#skF_7')),'#skF_6')
    | k3_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_7316])).

tff(c_7382,plain,(
    k3_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7381])).

tff(c_1937,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_3'('#skF_7'),C_93)
      | ~ r1_tarski(k1_xboole_0,C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_282])).

tff(c_7352,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_6')
    | ~ r1_tarski(k1_xboole_0,k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1937,c_7316])).

tff(c_7376,plain,(
    ~ r1_tarski(k1_xboole_0,k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_2729,c_7352])).

tff(c_7383,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7382,c_7376])).

tff(c_7392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_7383])).

tff(c_7393,plain,(
    r2_hidden('#skF_3'(k3_tarski('#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_7381])).

tff(c_10304,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10269,c_7393])).

tff(c_11141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_10304])).

tff(c_11143,plain,(
    ! [A_40132] : A_40132 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_10229])).

tff(c_11178,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11143,c_7393])).

tff(c_12015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_11178])).

tff(c_12017,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2251])).

tff(c_22859,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22850,c_12017])).

tff(c_22881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1516,c_22859])).

tff(c_23295,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22839])).

tff(c_23296,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_23295,c_12017])).

tff(c_23819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1516,c_23296])).

tff(c_23820,plain,(
    k1_tarski('#skF_3'('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1909])).

tff(c_23843,plain,(
    ! [D_104] :
      ( ~ r2_hidden(D_104,'#skF_3'('#skF_7'))
      | r2_hidden(D_104,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23820,c_339])).

tff(c_29466,plain,(
    ! [D_127560] :
      ( r2_hidden(D_127560,'#skF_6')
      | r2_hidden(D_127560,'#skF_6')
      | ~ r2_hidden(D_127560,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_2])).

tff(c_29536,plain,(
    ! [D_127885] :
      ( r2_hidden(D_127885,'#skF_6')
      | ~ r2_hidden(D_127885,'#skF_3'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_23843,c_29466])).

tff(c_29568,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_6')
    | ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_24692,c_29536])).

tff(c_29590,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_25901,c_29568])).

tff(c_24707,plain,(
    r2_hidden('#skF_3'('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_208])).

tff(c_24775,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_24707,c_525])).

tff(c_1618,plain,(
    ! [A_185] : k2_xboole_0('#skF_7',k2_tarski(A_185,'#skF_6')) = k2_tarski(A_185,'#skF_6') ),
    inference(resolution,[status(thm)],[c_196,c_1339])).

tff(c_1636,plain,(
    ! [D_6,A_185] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,k2_tarski(A_185,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1618,c_6])).

tff(c_25521,plain,(
    ! [C_109387] :
      ( k2_xboole_0(k1_xboole_0,C_109387) = C_109387
      | ~ r2_hidden('#skF_3'('#skF_8'),C_109387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_1042])).

tff(c_25551,plain,(
    ! [A_185] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski(A_185,'#skF_6')) = k2_tarski(A_185,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1636,c_25521])).

tff(c_25843,plain,(
    ! [A_109392] : k2_xboole_0(k1_xboole_0,k2_tarski(A_109392,'#skF_6')) = k2_tarski(A_109392,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24775,c_25551])).

tff(c_24695,plain,(
    ! [B_91] : r2_hidden('#skF_3'('#skF_8'),k2_xboole_0(k1_xboole_0,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_270])).

tff(c_25848,plain,(
    ! [A_109392] : r2_hidden('#skF_3'('#skF_8'),k2_tarski(A_109392,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25843,c_24695])).

tff(c_33693,plain,(
    ! [E_139738,B_139739,A_139740] :
      ( E_139738 = B_139739
      | E_139738 = A_139740
      | E_139738 = A_139740
      | ~ r2_hidden(E_139738,k2_tarski(A_139740,B_139739)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_33782,plain,(
    ! [A_109392] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | A_109392 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_25848,c_33693])).

tff(c_34112,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_33782])).

tff(c_34137,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34112,c_24707])).

tff(c_34147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1521,c_34137])).

tff(c_34282,plain,(
    ! [A_140882] : A_140882 = '#skF_3'('#skF_8') ),
    inference(splitRight,[status(thm)],[c_33782])).

tff(c_1438,plain,(
    ! [B_78] : k2_xboole_0('#skF_7',k2_tarski('#skF_6',B_78)) = k2_tarski('#skF_6',B_78) ),
    inference(resolution,[status(thm)],[c_193,c_1339])).

tff(c_23902,plain,(
    ! [B_109316] : r2_hidden('#skF_3'('#skF_7'),k2_xboole_0('#skF_7',B_109316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23820,c_270])).

tff(c_23909,plain,(
    ! [B_78] : r2_hidden('#skF_3'('#skF_7'),k2_tarski('#skF_6',B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_23902])).

tff(c_33792,plain,(
    ! [B_78] :
      ( B_78 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_23909,c_33693])).

tff(c_34034,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_33792])).

tff(c_24721,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_68])).

tff(c_29595,plain,
    ( r2_hidden('#skF_3'('#skF_3'('#skF_7')),'#skF_6')
    | '#skF_3'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_29536])).

tff(c_32067,plain,(
    '#skF_3'('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_29595])).

tff(c_32069,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32067,c_29590])).

tff(c_32098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24721,c_32069])).

tff(c_32099,plain,(
    r2_hidden('#skF_3'('#skF_3'('#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_29595])).

tff(c_34036,plain,(
    r2_hidden('#skF_3'('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34034,c_32099])).

tff(c_34308,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34282,c_34036])).

tff(c_35039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25901,c_34308])).

tff(c_35042,plain,(
    ! [B_149901] : B_149901 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_33792])).

tff(c_31493,plain,(
    ! [B_137772,C_137773] : k2_xboole_0('#skF_7',k1_enumset1('#skF_6',B_137772,C_137773)) = k1_enumset1('#skF_6',B_137772,C_137773) ),
    inference(resolution,[status(thm)],[c_32,c_1339])).

tff(c_33399,plain,(
    ! [D_139573,B_139574,C_139575] :
      ( ~ r2_hidden(D_139573,'#skF_7')
      | r2_hidden(D_139573,k1_enumset1('#skF_6',B_139574,C_139575)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31493,c_6])).

tff(c_24672,plain,(
    ! [C_151] :
      ( r1_tarski(k1_xboole_0,C_151)
      | ~ r2_hidden('#skF_3'('#skF_8'),C_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24665,c_1092])).

tff(c_33407,plain,(
    ! [B_139574,C_139575] :
      ( r1_tarski(k1_xboole_0,k1_enumset1('#skF_6',B_139574,C_139575))
      | ~ r2_hidden('#skF_3'('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_33399,c_24672])).

tff(c_33672,plain,(
    ! [B_139574,C_139575] : r1_tarski(k1_xboole_0,k1_enumset1('#skF_6',B_139574,C_139575)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24775,c_33407])).

tff(c_35059,plain,(
    r1_tarski(k1_xboole_0,'#skF_3'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35042,c_33672])).

tff(c_35957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29590,c_35059])).

tff(c_35958,plain,(
    r1_tarski(k1_xboole_0,k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_25206])).

tff(c_35963,plain,(
    k2_xboole_0(k1_xboole_0,k3_tarski('#skF_7')) = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_35958,c_22])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1267,plain,(
    ! [A_1,B_2] :
      ( r1_tarski('#skF_7',k2_xboole_0(A_1,B_2))
      | ~ r2_hidden('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_1177])).

tff(c_37454,plain,
    ( r1_tarski('#skF_7',k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6',k3_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35963,c_1267])).

tff(c_37474,plain,(
    ~ r2_hidden('#skF_6',k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_36032,c_37454])).

tff(c_46811,plain,(
    ! [E_210300,B_210301,A_210302] :
      ( E_210300 = B_210301
      | E_210300 = A_210302
      | E_210300 = A_210302
      | ~ r2_hidden(E_210300,k2_tarski(A_210302,B_210301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_46900,plain,(
    ! [A_109392] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | A_109392 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_25848,c_46811])).

tff(c_47229,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_46900])).

tff(c_37448,plain,(
    r2_hidden('#skF_3'('#skF_8'),k3_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35963,c_24695])).

tff(c_47235,plain,(
    r2_hidden('#skF_6',k3_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47229,c_37448])).

tff(c_47259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37474,c_47235])).

tff(c_47583,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46900])).

tff(c_47584,plain,(
    r2_hidden('#skF_6',k3_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47583,c_37448])).

tff(c_48193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37474,c_47584])).

tff(c_48194,plain,(
    k1_tarski('#skF_3'('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_24664])).

tff(c_48430,plain,(
    ! [C_220687] :
      ( r1_tarski('#skF_7',C_220687)
      | ~ r2_hidden('#skF_3'('#skF_8'),C_220687) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48194,c_1092])).

tff(c_48517,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_48430])).

tff(c_48565,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_48517])).

tff(c_48572,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48565,c_22])).

tff(c_48573,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48572,c_513])).

tff(c_48575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_48573])).

tff(c_48595,plain,(
    ! [B_220688] : r1_tarski('#skF_7',k1_tarski(B_220688)) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_48598,plain,(
    ! [B_220688] :
      ( k1_tarski(B_220688) = '#skF_7'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_48595,c_64])).

tff(c_48606,plain,(
    ! [B_220688] : k1_tarski(B_220688) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_48598])).

tff(c_216,plain,(
    ! [B_84] : k2_xboole_0(k1_tarski(B_84),k1_tarski(B_84)) = k1_tarski(B_84) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_222,plain,(
    ! [B_84] : k3_tarski(k1_tarski(k1_tarski(B_84))) = k1_tarski(B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_117])).

tff(c_534,plain,(
    k3_tarski(k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_222])).

tff(c_564,plain,(
    k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_534])).

tff(c_48615,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48606,c_564])).

tff(c_120,plain,(
    ! [A_72] : k3_tarski(k1_tarski(A_72)) = k2_xboole_0(A_72,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_108])).

tff(c_129,plain,(
    ! [A_72] : r1_tarski(A_72,k3_tarski(k1_tarski(A_72))) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_24])).

tff(c_48629,plain,(
    ! [A_72] : r1_tarski(A_72,k3_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48606,c_129])).

tff(c_48764,plain,(
    ! [A_72] : r1_tarski(A_72,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48615,c_48629])).

tff(c_48875,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48764,c_563])).

tff(c_48577,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_1106,plain,(
    ! [C_151] :
      ( k2_xboole_0('#skF_7',C_151) = C_151
      | ~ r2_hidden('#skF_6',C_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_1043])).

tff(c_48587,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48577,c_1106])).

tff(c_48876,plain,
    ( k2_xboole_0('#skF_7','#skF_8') = k1_xboole_0
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_48875,c_48587])).

tff(c_49062,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_48876])).

tff(c_49064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_49062])).

tff(c_49066,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_1172,plain,(
    ! [C_153] :
      ( r1_tarski('#skF_7',C_153)
      | ~ r2_hidden('#skF_6',C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_1155])).

tff(c_49075,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_49066,c_1172])).

tff(c_70672,plain,(
    ! [A_309186] : k2_xboole_0(k1_xboole_0,k2_tarski(A_309186,'#skF_6')) = k2_tarski(A_309186,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69289,c_70520])).

tff(c_70677,plain,(
    ! [A_309186] : r2_hidden('#skF_3'('#skF_8'),k2_tarski(A_309186,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70672,c_69152])).

tff(c_77778,plain,(
    ! [E_341145,B_341146,A_341147] :
      ( E_341145 = B_341146
      | E_341145 = A_341147
      | E_341145 = A_341147
      | ~ r2_hidden(E_341145,k2_tarski(A_341147,B_341146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_77867,plain,(
    ! [A_309186] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | A_309186 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70677,c_77778])).

tff(c_77963,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_77867])).

tff(c_1263,plain,(
    ! [A_20] :
      ( r1_tarski('#skF_7',k3_tarski(k1_tarski(A_20)))
      | ~ r2_hidden('#skF_6',A_20) ) ),
    inference(resolution,[status(thm)],[c_339,c_1177])).

tff(c_69126,plain,
    ( r1_tarski('#skF_7',k3_tarski(k1_xboole_0))
    | ~ r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69122,c_1263])).

tff(c_70666,plain,(
    ~ r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_69126])).

tff(c_70671,plain,(
    ~ r1_tarski('#skF_7','#skF_3'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_528,c_70666])).

tff(c_77970,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77963,c_70671])).

tff(c_77995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49075,c_77970])).

tff(c_77997,plain,(
    '#skF_3'('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77867])).

tff(c_78130,plain,(
    ! [A_342287] : A_342287 = '#skF_3'('#skF_8') ),
    inference(splitRight,[status(thm)],[c_77867])).

tff(c_49661,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_49647])).

tff(c_49672,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_49661])).

tff(c_49673,plain,(
    k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_49672])).

tff(c_49715,plain,(
    r2_hidden('#skF_3'('#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_208])).

tff(c_49793,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_49715,c_525])).

tff(c_49235,plain,(
    ! [B_223686] : k2_xboole_0('#skF_7',k2_tarski('#skF_6',B_223686)) = k2_tarski('#skF_6',B_223686) ),
    inference(resolution,[status(thm)],[c_193,c_1339])).

tff(c_49249,plain,(
    ! [D_6,B_223686] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,k2_tarski('#skF_6',B_223686)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49235,c_6])).

tff(c_59323,plain,(
    ! [C_265730] :
      ( k2_xboole_0(k1_xboole_0,C_265730) = C_265730
      | ~ r2_hidden('#skF_3'('#skF_7'),C_265730) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_1042])).

tff(c_59353,plain,(
    ! [B_223686] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski('#skF_6',B_223686)) = k2_tarski('#skF_6',B_223686)
      | ~ r2_hidden('#skF_3'('#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_49249,c_59323])).

tff(c_65990,plain,(
    ! [B_296237] : k2_xboole_0(k1_xboole_0,k2_tarski('#skF_6',B_296237)) = k2_tarski('#skF_6',B_296237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49793,c_59353])).

tff(c_49703,plain,(
    ! [B_91] : r2_hidden('#skF_3'('#skF_7'),k2_xboole_0(k1_xboole_0,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_270])).

tff(c_66001,plain,(
    ! [B_296237] : r2_hidden('#skF_3'('#skF_7'),k2_tarski('#skF_6',B_296237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65990,c_49703])).

tff(c_66994,plain,(
    ! [E_298037,B_298038,A_298039] :
      ( E_298037 = B_298038
      | E_298037 = A_298039
      | E_298037 = A_298039
      | ~ r2_hidden(E_298037,k2_tarski(A_298039,B_298038)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_67075,plain,(
    ! [B_296237] :
      ( B_296237 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_66001,c_66994])).

tff(c_67095,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_67075])).

tff(c_67128,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67095,c_49715])).

tff(c_67146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49067,c_67128])).

tff(c_67654,plain,(
    '#skF_3'('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_67075])).

tff(c_50535,plain,(
    ! [C_223743] :
      ( k2_xboole_0(k1_xboole_0,C_223743) = C_223743
      | ~ r2_hidden('#skF_3'('#skF_7'),C_223743) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_1042])).

tff(c_50565,plain,(
    ! [A_223691] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski(A_223691,'#skF_6')) = k2_tarski(A_223691,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_49351,c_50535])).

tff(c_53543,plain,(
    ! [A_233128] : k2_xboole_0(k1_xboole_0,k2_tarski(A_233128,'#skF_6')) = k2_tarski(A_233128,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49793,c_50565])).

tff(c_53554,plain,(
    ! [A_233128] : r2_hidden('#skF_3'('#skF_7'),k2_tarski(A_233128,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53543,c_49703])).

tff(c_58063,plain,(
    ! [E_254596,B_254597,A_254598] :
      ( E_254596 = B_254597
      | E_254596 = A_254598
      | E_254596 = A_254598
      | ~ r2_hidden(E_254596,k2_tarski(A_254598,B_254597)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_992])).

tff(c_58152,plain,(
    ! [A_233128] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | A_233128 = '#skF_3'('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_53554,c_58063])).

tff(c_58172,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_58152])).

tff(c_49677,plain,
    ( r1_tarski('#skF_7',k3_tarski(k1_xboole_0))
    | ~ r2_hidden('#skF_6','#skF_3'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_1263])).

tff(c_50482,plain,(
    ~ r2_hidden('#skF_6','#skF_3'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_49677])).

tff(c_50486,plain,(
    ~ r1_tarski('#skF_7','#skF_3'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_528,c_50482])).

tff(c_58181,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58172,c_50486])).

tff(c_58204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49075,c_58181])).

tff(c_58206,plain,(
    '#skF_3'('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58152])).

tff(c_58224,plain,(
    ! [A_255087] : A_255087 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_58152])).

tff(c_49074,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_49066,c_1106])).

tff(c_49155,plain,(
    ! [D_223680] :
      ( ~ r2_hidden(D_223680,'#skF_7')
      | r2_hidden(D_223680,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49074,c_6])).

tff(c_49169,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_49155])).

tff(c_49178,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_49169])).

tff(c_50006,plain,(
    ! [C_223721] :
      ( r1_tarski(k1_xboole_0,C_223721)
      | ~ r2_hidden('#skF_3'('#skF_7'),C_223721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49673,c_1092])).

tff(c_50132,plain,(
    r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_49178,c_50006])).

tff(c_50163,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50132,c_22])).

tff(c_58733,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_58224,c_50163])).

tff(c_59171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58206,c_58733])).

tff(c_59173,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_49677])).

tff(c_59185,plain,(
    r1_tarski('#skF_7','#skF_3'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_59173,c_1172])).

tff(c_67655,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_67654,c_59185])).

tff(c_68275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49079,c_67655])).

tff(c_68276,plain,(
    k1_tarski('#skF_3'('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_49672])).

tff(c_68364,plain,(
    ! [B_309111] : r2_hidden('#skF_3'('#skF_7'),k2_xboole_0('#skF_7',B_309111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68276,c_270])).

tff(c_68371,plain,(
    ! [B_78] : r2_hidden('#skF_3'('#skF_7'),k2_tarski('#skF_6',B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1438,c_68364])).

tff(c_77877,plain,(
    ! [B_78] :
      ( B_78 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_68371,c_77778])).

tff(c_77887,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_77877])).

tff(c_78166,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_78130,c_77887])).

tff(c_78930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77997,c_78166])).

tff(c_78932,plain,(
    '#skF_3'('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77877])).

tff(c_78933,plain,(
    ! [B_351954] : B_351954 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_77877])).

tff(c_49108,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49074,c_6])).

tff(c_69300,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_69289,c_49108])).

tff(c_69406,plain,(
    ! [C_309158] :
      ( r1_tarski(k1_xboole_0,C_309158)
      | ~ r2_hidden('#skF_3'('#skF_8'),C_309158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69122,c_1092])).

tff(c_69518,plain,(
    r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_69300,c_69406])).

tff(c_69568,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_69518,c_22])).

tff(c_79210,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_78933,c_69568])).

tff(c_79891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78932,c_79210])).

tff(c_79893,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_69126])).

tff(c_79922,plain,(
    r1_tarski('#skF_7','#skF_3'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_79893,c_1172])).

tff(c_87481,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87480,c_79922])).

tff(c_88123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49079,c_87481])).

tff(c_88124,plain,(
    k1_tarski('#skF_3'('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_69121])).

tff(c_88350,plain,(
    ! [C_404764] :
      ( r1_tarski('#skF_7',C_404764)
      | ~ r2_hidden('#skF_3'('#skF_8'),C_404764) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88124,c_1092])).

tff(c_88448,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_88350])).

tff(c_88507,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_88448])).

tff(c_88570,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88507,c_22])).

tff(c_88571,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88570,c_513])).

tff(c_88573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_88571])).

tff(c_88605,plain,(
    ! [B_404769] : r1_tarski('#skF_7',k1_tarski(B_404769)) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_88608,plain,(
    ! [B_404769] :
      ( k1_tarski(B_404769) = '#skF_7'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_88605,c_64])).

tff(c_88616,plain,(
    ! [B_404769] : k1_tarski(B_404769) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_88608])).

tff(c_88625,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88616,c_564])).

tff(c_88639,plain,(
    ! [A_72] : r1_tarski(A_72,k3_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88616,c_129])).

tff(c_88917,plain,(
    ! [A_72] : r1_tarski(A_72,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88625,c_88639])).

tff(c_88981,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88917,c_563])).

tff(c_88575,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_88597,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88575,c_1106])).

tff(c_88982,plain,
    ( k2_xboole_0('#skF_7','#skF_8') = k1_xboole_0
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_88981,c_88597])).

tff(c_89169,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_88982])).

tff(c_89171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_89169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.14/9.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.30/9.55  
% 18.30/9.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.30/9.55  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 18.30/9.55  
% 18.30/9.55  %Foreground sorts:
% 18.30/9.55  
% 18.30/9.55  
% 18.30/9.55  %Background operators:
% 18.30/9.55  
% 18.30/9.55  
% 18.30/9.55  %Foreground operators:
% 18.30/9.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.30/9.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.30/9.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.30/9.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.30/9.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.30/9.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.30/9.55  tff('#skF_7', type, '#skF_7': $i).
% 18.30/9.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.30/9.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.30/9.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.30/9.55  tff('#skF_6', type, '#skF_6': $i).
% 18.30/9.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.30/9.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.30/9.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.30/9.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 18.30/9.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.30/9.55  tff('#skF_8', type, '#skF_8': $i).
% 18.30/9.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.30/9.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.30/9.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 18.30/9.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 18.30/9.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.30/9.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.30/9.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.30/9.55  
% 18.56/9.59  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 18.56/9.59  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.56/9.59  tff(f_83, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 18.56/9.59  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.56/9.59  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 18.56/9.59  tff(f_91, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 18.56/9.59  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.56/9.59  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 18.56/9.59  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 18.56/9.59  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 18.56/9.59  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.56/9.59  tff(c_82, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 18.56/9.59  tff(c_80, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 18.56/9.59  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 18.56/9.59  tff(c_99, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.56/9.59  tff(c_102, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_99])).
% 18.56/9.59  tff(c_492, plain, (![B_124, A_125]: (k1_tarski(B_124)=A_125 | k1_xboole_0=A_125 | ~r1_tarski(A_125, k1_tarski(B_124)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.56/9.59  tff(c_498, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_102, c_492])).
% 18.56/9.59  tff(c_506, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_80, c_498])).
% 18.56/9.59  tff(c_513, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_84])).
% 18.56/9.59  tff(c_78, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 18.56/9.59  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.56/9.59  tff(c_50, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.56/9.59  tff(c_271, plain, (![A_92, C_93, B_94]: (r2_hidden(A_92, C_93) | ~r1_tarski(k2_tarski(A_92, B_94), C_93))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.56/9.59  tff(c_282, plain, (![A_20, C_93]: (r2_hidden(A_20, C_93) | ~r1_tarski(k1_tarski(A_20), C_93))), inference(superposition, [status(thm), theory('equality')], [c_50, c_271])).
% 18.56/9.59  tff(c_528, plain, (![C_93]: (r2_hidden('#skF_6', C_93) | ~r1_tarski('#skF_7', C_93))), inference(superposition, [status(thm), theory('equality')], [c_506, c_282])).
% 18.56/9.59  tff(c_68, plain, (![B_49]: (r1_tarski(k1_xboole_0, k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.56/9.59  tff(c_140, plain, (![A_73, B_74]: (k2_xboole_0(A_73, B_74)=B_74 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.56/9.59  tff(c_156, plain, (![B_49]: (k2_xboole_0(k1_xboole_0, k1_tarski(B_49))=k1_tarski(B_49))), inference(resolution, [status(thm)], [c_68, c_140])).
% 18.56/9.59  tff(c_350, plain, (![D_110, A_111, B_112]: (~r2_hidden(D_110, A_111) | r2_hidden(D_110, k2_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.56/9.59  tff(c_359, plain, (![D_110, B_49]: (~r2_hidden(D_110, k1_xboole_0) | r2_hidden(D_110, k1_tarski(B_49)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_350])).
% 18.56/9.59  tff(c_813, plain, (![A_137, B_138, C_139]: (r1_tarski(k2_tarski(A_137, B_138), C_139) | ~r2_hidden(B_138, C_139) | ~r2_hidden(A_137, C_139))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.56/9.59  tff(c_1021, plain, (![A_148, C_149]: (r1_tarski(k1_tarski(A_148), C_149) | ~r2_hidden(A_148, C_149) | ~r2_hidden(A_148, C_149))), inference(superposition, [status(thm), theory('equality')], [c_50, c_813])).
% 18.56/9.59  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.56/9.59  tff(c_1043, plain, (![A_150, C_151]: (k2_xboole_0(k1_tarski(A_150), C_151)=C_151 | ~r2_hidden(A_150, C_151))), inference(resolution, [status(thm)], [c_1021, c_22])).
% 18.56/9.59  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.56/9.59  tff(c_1155, plain, (![A_152, C_153]: (r1_tarski(k1_tarski(A_152), C_153) | ~r2_hidden(A_152, C_153))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_24])).
% 18.56/9.59  tff(c_1177, plain, (![C_154]: (r1_tarski('#skF_7', C_154) | ~r2_hidden('#skF_6', C_154))), inference(superposition, [status(thm), theory('equality')], [c_506, c_1155])).
% 18.56/9.59  tff(c_1264, plain, (![B_49]: (r1_tarski('#skF_7', k1_tarski(B_49)) | ~r2_hidden('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_359, c_1177])).
% 18.56/9.59  tff(c_49067, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_49079, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_528, c_49067])).
% 18.56/9.59  tff(c_327, plain, (![D_104, B_105, A_106]: (~r2_hidden(D_104, B_105) | r2_hidden(D_104, k2_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.56/9.59  tff(c_342, plain, (![D_104]: (~r2_hidden(D_104, '#skF_8') | r2_hidden(D_104, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_327])).
% 18.56/9.59  tff(c_510, plain, (![D_104]: (~r2_hidden(D_104, '#skF_8') | r2_hidden(D_104, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_342])).
% 18.56/9.59  tff(c_64, plain, (![B_49, A_48]: (k1_tarski(B_49)=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.56/9.59  tff(c_517, plain, (![A_48]: (k1_tarski('#skF_6')=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_506, c_64])).
% 18.56/9.59  tff(c_563, plain, (![A_48]: (A_48='#skF_7' | k1_xboole_0=A_48 | ~r1_tarski(A_48, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_517])).
% 18.56/9.59  tff(c_49647, plain, (![A_223704]: (k1_tarski(A_223704)='#skF_7' | k1_tarski(A_223704)=k1_xboole_0 | ~r2_hidden(A_223704, '#skF_7'))), inference(resolution, [status(thm)], [c_1021, c_563])).
% 18.56/9.59  tff(c_69100, plain, (![D_309147]: (k1_tarski(D_309147)='#skF_7' | k1_tarski(D_309147)=k1_xboole_0 | ~r2_hidden(D_309147, '#skF_8'))), inference(resolution, [status(thm)], [c_510, c_49647])).
% 18.56/9.59  tff(c_69112, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_69100])).
% 18.56/9.59  tff(c_69121, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_69112])).
% 18.56/9.59  tff(c_69122, plain, (k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_69121])).
% 18.56/9.59  tff(c_187, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.56/9.59  tff(c_32, plain, (![E_19, B_14, C_15]: (r2_hidden(E_19, k1_enumset1(E_19, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.56/9.59  tff(c_205, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_32])).
% 18.56/9.59  tff(c_208, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_205])).
% 18.56/9.59  tff(c_69164, plain, (r2_hidden('#skF_3'('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69122, c_208])).
% 18.56/9.59  tff(c_525, plain, (![D_110]: (~r2_hidden(D_110, k1_xboole_0) | r2_hidden(D_110, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_506, c_359])).
% 18.56/9.59  tff(c_69289, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_69164, c_525])).
% 18.56/9.59  tff(c_28, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.56/9.59  tff(c_196, plain, (![B_78, A_77]: (r2_hidden(B_78, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_28])).
% 18.56/9.59  tff(c_1339, plain, (![C_168]: (k2_xboole_0('#skF_7', C_168)=C_168 | ~r2_hidden('#skF_6', C_168))), inference(superposition, [status(thm), theory('equality')], [c_506, c_1043])).
% 18.56/9.59  tff(c_49333, plain, (![A_223691]: (k2_xboole_0('#skF_7', k2_tarski(A_223691, '#skF_6'))=k2_tarski(A_223691, '#skF_6'))), inference(resolution, [status(thm)], [c_196, c_1339])).
% 18.56/9.59  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.56/9.59  tff(c_49351, plain, (![D_6, A_223691]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, k2_tarski(A_223691, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_49333, c_6])).
% 18.56/9.59  tff(c_1042, plain, (![A_148, C_149]: (k2_xboole_0(k1_tarski(A_148), C_149)=C_149 | ~r2_hidden(A_148, C_149))), inference(resolution, [status(thm)], [c_1021, c_22])).
% 18.56/9.59  tff(c_70480, plain, (![C_309185]: (k2_xboole_0(k1_xboole_0, C_309185)=C_309185 | ~r2_hidden('#skF_3'('#skF_8'), C_309185))), inference(superposition, [status(thm), theory('equality')], [c_69122, c_1042])).
% 18.56/9.59  tff(c_70520, plain, (![A_223691]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_223691, '#skF_6'))=k2_tarski(A_223691, '#skF_6') | ~r2_hidden('#skF_3'('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_49351, c_70480])).
% 18.56/9.59  tff(c_86940, plain, (![A_394489]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_394489, '#skF_6'))=k2_tarski(A_394489, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69289, c_70520])).
% 18.56/9.59  tff(c_235, plain, (![B_85, C_86, A_87]: (r2_hidden(B_85, C_86) | ~r1_tarski(k2_tarski(A_87, B_85), C_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.56/9.59  tff(c_263, plain, (![B_89, A_90, B_91]: (r2_hidden(B_89, k2_xboole_0(k2_tarski(A_90, B_89), B_91)))), inference(resolution, [status(thm)], [c_24, c_235])).
% 18.56/9.59  tff(c_270, plain, (![A_20, B_91]: (r2_hidden(A_20, k2_xboole_0(k1_tarski(A_20), B_91)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_263])).
% 18.56/9.59  tff(c_69152, plain, (![B_91]: (r2_hidden('#skF_3'('#skF_8'), k2_xboole_0(k1_xboole_0, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_69122, c_270])).
% 18.56/9.59  tff(c_86945, plain, (![A_394489]: (r2_hidden('#skF_3'('#skF_8'), k2_tarski(A_394489, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_86940, c_69152])).
% 18.56/9.59  tff(c_52, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.56/9.59  tff(c_992, plain, (![E_144, C_145, B_146, A_147]: (E_144=C_145 | E_144=B_146 | E_144=A_147 | ~r2_hidden(E_144, k1_enumset1(A_147, B_146, C_145)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.56/9.59  tff(c_87007, plain, (![E_394815, B_394816, A_394817]: (E_394815=B_394816 | E_394815=A_394817 | E_394815=A_394817 | ~r2_hidden(E_394815, k2_tarski(A_394817, B_394816)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_87083, plain, (![A_394489]: ('#skF_3'('#skF_8')='#skF_6' | A_394489='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_86945, c_87007])).
% 18.56/9.59  tff(c_87183, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_87083])).
% 18.56/9.59  tff(c_87214, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87183, c_69164])).
% 18.56/9.59  tff(c_87230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49067, c_87214])).
% 18.56/9.59  tff(c_87480, plain, ('#skF_3'('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_87083])).
% 18.56/9.59  tff(c_108, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.56/9.59  tff(c_117, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_50, c_108])).
% 18.56/9.59  tff(c_339, plain, (![D_104, A_20]: (~r2_hidden(D_104, A_20) | r2_hidden(D_104, k3_tarski(k1_tarski(A_20))))), inference(superposition, [status(thm), theory('equality')], [c_117, c_327])).
% 18.56/9.59  tff(c_523, plain, (![D_104]: (~r2_hidden(D_104, '#skF_6') | r2_hidden(D_104, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_506, c_339])).
% 18.56/9.59  tff(c_1255, plain, (r1_tarski('#skF_7', k3_tarski('#skF_7')) | ~r2_hidden('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_523, c_1177])).
% 18.56/9.59  tff(c_1516, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_1255])).
% 18.56/9.59  tff(c_552, plain, (k2_xboole_0('#skF_6', '#skF_6')=k3_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_506, c_117])).
% 18.56/9.59  tff(c_2, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.56/9.59  tff(c_35964, plain, (![D_160324]: (r2_hidden(D_160324, '#skF_6') | r2_hidden(D_160324, '#skF_6') | ~r2_hidden(D_160324, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_552, c_2])).
% 18.56/9.59  tff(c_36010, plain, (r2_hidden('#skF_6', '#skF_6') | ~r1_tarski('#skF_7', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_528, c_35964])).
% 18.56/9.59  tff(c_36032, plain, (~r1_tarski('#skF_7', k3_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1516, c_1516, c_36010])).
% 18.56/9.59  tff(c_1884, plain, (![A_198]: (k1_tarski(A_198)='#skF_7' | k1_tarski(A_198)=k1_xboole_0 | ~r2_hidden(A_198, '#skF_7'))), inference(resolution, [status(thm)], [c_1155, c_563])).
% 18.56/9.59  tff(c_24643, plain, (![D_109359]: (k1_tarski(D_109359)='#skF_7' | k1_tarski(D_109359)=k1_xboole_0 | ~r2_hidden(D_109359, '#skF_8'))), inference(resolution, [status(thm)], [c_510, c_1884])).
% 18.56/9.59  tff(c_24655, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_24643])).
% 18.56/9.59  tff(c_24664, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_24655])).
% 18.56/9.59  tff(c_24665, plain, (k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24664])).
% 18.56/9.59  tff(c_1092, plain, (![A_150, C_151]: (r1_tarski(k1_tarski(A_150), C_151) | ~r2_hidden(A_150, C_151))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_24])).
% 18.56/9.59  tff(c_25090, plain, (![C_109372]: (r1_tarski(k1_xboole_0, C_109372) | ~r2_hidden('#skF_3'('#skF_8'), C_109372))), inference(superposition, [status(thm), theory('equality')], [c_24665, c_1092])).
% 18.56/9.59  tff(c_25206, plain, (r1_tarski(k1_xboole_0, k3_tarski('#skF_7')) | ~r2_hidden('#skF_3'('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_523, c_25090])).
% 18.56/9.59  tff(c_25901, plain, (~r2_hidden('#skF_3'('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_25206])).
% 18.56/9.59  tff(c_24692, plain, (![C_93]: (r2_hidden('#skF_3'('#skF_8'), C_93) | ~r1_tarski(k1_xboole_0, C_93))), inference(superposition, [status(thm), theory('equality')], [c_24665, c_282])).
% 18.56/9.59  tff(c_1898, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_1884])).
% 18.56/9.59  tff(c_1909, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_1898])).
% 18.56/9.59  tff(c_1910, plain, (k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1909])).
% 18.56/9.59  tff(c_1952, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1910, c_208])).
% 18.56/9.59  tff(c_2055, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_1952, c_525])).
% 18.56/9.59  tff(c_193, plain, (![A_77, B_78]: (r2_hidden(A_77, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_32])).
% 18.56/9.59  tff(c_1545, plain, (![B_181]: (k2_xboole_0('#skF_7', k2_tarski('#skF_6', B_181))=k2_tarski('#skF_6', B_181))), inference(resolution, [status(thm)], [c_193, c_1339])).
% 18.56/9.59  tff(c_1559, plain, (![D_6, B_181]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, k2_tarski('#skF_6', B_181)))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_6])).
% 18.56/9.59  tff(c_2441, plain, (![C_225]: (k2_xboole_0(k1_xboole_0, C_225)=C_225 | ~r2_hidden('#skF_3'('#skF_7'), C_225))), inference(superposition, [status(thm), theory('equality')], [c_1910, c_1042])).
% 18.56/9.59  tff(c_2460, plain, (![B_181]: (k2_xboole_0(k1_xboole_0, k2_tarski('#skF_6', B_181))=k2_tarski('#skF_6', B_181) | ~r2_hidden('#skF_3'('#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_1559, c_2441])).
% 18.56/9.59  tff(c_12297, plain, (![B_50242]: (k2_xboole_0(k1_xboole_0, k2_tarski('#skF_6', B_50242))=k2_tarski('#skF_6', B_50242))), inference(demodulation, [status(thm), theory('equality')], [c_2055, c_2460])).
% 18.56/9.59  tff(c_1940, plain, (![B_91]: (r2_hidden('#skF_3'('#skF_7'), k2_xboole_0(k1_xboole_0, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_1910, c_270])).
% 18.56/9.59  tff(c_12306, plain, (![B_50242]: (r2_hidden('#skF_3'('#skF_7'), k2_tarski('#skF_6', B_50242)))), inference(superposition, [status(thm), theory('equality')], [c_12297, c_1940])).
% 18.56/9.59  tff(c_22741, plain, (![E_98890, B_98891, A_98892]: (E_98890=B_98891 | E_98890=A_98892 | E_98890=A_98892 | ~r2_hidden(E_98890, k2_tarski(A_98892, B_98891)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_22839, plain, (![B_50242]: (B_50242='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_12306, c_22741])).
% 18.56/9.59  tff(c_22850, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_22839])).
% 18.56/9.59  tff(c_2144, plain, (![C_211]: (r1_tarski(k1_xboole_0, C_211) | ~r2_hidden('#skF_3'('#skF_7'), C_211))), inference(superposition, [status(thm), theory('equality')], [c_1910, c_1092])).
% 18.56/9.59  tff(c_2251, plain, (r1_tarski(k1_xboole_0, k3_tarski('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_523, c_2144])).
% 18.56/9.59  tff(c_2729, plain, (~r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2251])).
% 18.56/9.59  tff(c_1521, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_9119, plain, (![A_28720, B_28721]: (k2_xboole_0('#skF_7', k1_enumset1(A_28720, B_28721, '#skF_6'))=k1_enumset1(A_28720, B_28721, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_1339])).
% 18.56/9.59  tff(c_9439, plain, (![D_28884, A_28885, B_28886]: (~r2_hidden(D_28884, '#skF_7') | r2_hidden(D_28884, k1_enumset1(A_28885, B_28886, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9119, c_6])).
% 18.56/9.59  tff(c_26, plain, (![E_19, C_15, B_14, A_13]: (E_19=C_15 | E_19=B_14 | E_19=A_13 | ~r2_hidden(E_19, k1_enumset1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.56/9.59  tff(c_9966, plain, (![D_29213, B_29214, A_29215]: (D_29213='#skF_6' | D_29213=B_29214 | D_29213=A_29215 | ~r2_hidden(D_29213, '#skF_7'))), inference(resolution, [status(thm)], [c_9439, c_26])).
% 18.56/9.59  tff(c_10005, plain, (![B_29214, A_29215]: ('#skF_3'('#skF_7')='#skF_6' | B_29214='#skF_3'('#skF_7') | A_29215='#skF_3'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_9966])).
% 18.56/9.59  tff(c_10029, plain, (![B_29214, A_29215]: ('#skF_3'('#skF_7')='#skF_6' | B_29214='#skF_3'('#skF_7') | A_29215='#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_10005])).
% 18.56/9.59  tff(c_10194, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_10029])).
% 18.56/9.59  tff(c_10219, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10194, c_1952])).
% 18.56/9.59  tff(c_10228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1521, c_10219])).
% 18.56/9.59  tff(c_10229, plain, (![A_29215, B_29214]: (A_29215='#skF_3'('#skF_7') | B_29214='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_10029])).
% 18.56/9.59  tff(c_10269, plain, (![B_30033]: (B_30033='#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_10229])).
% 18.56/9.59  tff(c_66, plain, (![B_49]: (r1_tarski(k1_tarski(B_49), k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.56/9.59  tff(c_1964, plain, (r1_tarski(k1_tarski('#skF_3'('#skF_7')), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1910, c_66])).
% 18.56/9.59  tff(c_1977, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1964])).
% 18.56/9.59  tff(c_7316, plain, (![D_18617]: (r2_hidden(D_18617, '#skF_6') | r2_hidden(D_18617, '#skF_6') | ~r2_hidden(D_18617, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_552, c_2])).
% 18.56/9.59  tff(c_7381, plain, (r2_hidden('#skF_3'(k3_tarski('#skF_7')), '#skF_6') | k3_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_7316])).
% 18.56/9.59  tff(c_7382, plain, (k3_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7381])).
% 18.56/9.59  tff(c_1937, plain, (![C_93]: (r2_hidden('#skF_3'('#skF_7'), C_93) | ~r1_tarski(k1_xboole_0, C_93))), inference(superposition, [status(thm), theory('equality')], [c_1910, c_282])).
% 18.56/9.59  tff(c_7352, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6') | ~r1_tarski(k1_xboole_0, k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1937, c_7316])).
% 18.56/9.59  tff(c_7376, plain, (~r1_tarski(k1_xboole_0, k3_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2729, c_2729, c_7352])).
% 18.56/9.59  tff(c_7383, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7382, c_7376])).
% 18.56/9.59  tff(c_7392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1977, c_7383])).
% 18.56/9.59  tff(c_7393, plain, (r2_hidden('#skF_3'(k3_tarski('#skF_7')), '#skF_6')), inference(splitRight, [status(thm)], [c_7381])).
% 18.56/9.59  tff(c_10304, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10269, c_7393])).
% 18.56/9.59  tff(c_11141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2729, c_10304])).
% 18.56/9.59  tff(c_11143, plain, (![A_40132]: (A_40132='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_10229])).
% 18.56/9.59  tff(c_11178, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11143, c_7393])).
% 18.56/9.59  tff(c_12015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2729, c_11178])).
% 18.56/9.59  tff(c_12017, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_2251])).
% 18.56/9.59  tff(c_22859, plain, (r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22850, c_12017])).
% 18.56/9.59  tff(c_22881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1516, c_22859])).
% 18.56/9.59  tff(c_23295, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_22839])).
% 18.56/9.59  tff(c_23296, plain, (r2_hidden('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_23295, c_12017])).
% 18.56/9.59  tff(c_23819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1516, c_23296])).
% 18.56/9.59  tff(c_23820, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_1909])).
% 18.56/9.59  tff(c_23843, plain, (![D_104]: (~r2_hidden(D_104, '#skF_3'('#skF_7')) | r2_hidden(D_104, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_23820, c_339])).
% 18.56/9.59  tff(c_29466, plain, (![D_127560]: (r2_hidden(D_127560, '#skF_6') | r2_hidden(D_127560, '#skF_6') | ~r2_hidden(D_127560, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_552, c_2])).
% 18.56/9.59  tff(c_29536, plain, (![D_127885]: (r2_hidden(D_127885, '#skF_6') | ~r2_hidden(D_127885, '#skF_3'('#skF_7')))), inference(resolution, [status(thm)], [c_23843, c_29466])).
% 18.56/9.59  tff(c_29568, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_6') | ~r1_tarski(k1_xboole_0, '#skF_3'('#skF_7'))), inference(resolution, [status(thm)], [c_24692, c_29536])).
% 18.56/9.59  tff(c_29590, plain, (~r1_tarski(k1_xboole_0, '#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_25901, c_29568])).
% 18.56/9.59  tff(c_24707, plain, (r2_hidden('#skF_3'('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24665, c_208])).
% 18.56/9.59  tff(c_24775, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_24707, c_525])).
% 18.56/9.59  tff(c_1618, plain, (![A_185]: (k2_xboole_0('#skF_7', k2_tarski(A_185, '#skF_6'))=k2_tarski(A_185, '#skF_6'))), inference(resolution, [status(thm)], [c_196, c_1339])).
% 18.56/9.59  tff(c_1636, plain, (![D_6, A_185]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, k2_tarski(A_185, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1618, c_6])).
% 18.56/9.59  tff(c_25521, plain, (![C_109387]: (k2_xboole_0(k1_xboole_0, C_109387)=C_109387 | ~r2_hidden('#skF_3'('#skF_8'), C_109387))), inference(superposition, [status(thm), theory('equality')], [c_24665, c_1042])).
% 18.56/9.59  tff(c_25551, plain, (![A_185]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_185, '#skF_6'))=k2_tarski(A_185, '#skF_6') | ~r2_hidden('#skF_3'('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_1636, c_25521])).
% 18.56/9.59  tff(c_25843, plain, (![A_109392]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_109392, '#skF_6'))=k2_tarski(A_109392, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24775, c_25551])).
% 18.56/9.59  tff(c_24695, plain, (![B_91]: (r2_hidden('#skF_3'('#skF_8'), k2_xboole_0(k1_xboole_0, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_24665, c_270])).
% 18.56/9.59  tff(c_25848, plain, (![A_109392]: (r2_hidden('#skF_3'('#skF_8'), k2_tarski(A_109392, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_25843, c_24695])).
% 18.56/9.59  tff(c_33693, plain, (![E_139738, B_139739, A_139740]: (E_139738=B_139739 | E_139738=A_139740 | E_139738=A_139740 | ~r2_hidden(E_139738, k2_tarski(A_139740, B_139739)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_33782, plain, (![A_109392]: ('#skF_3'('#skF_8')='#skF_6' | A_109392='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_25848, c_33693])).
% 18.56/9.59  tff(c_34112, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_33782])).
% 18.56/9.59  tff(c_34137, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34112, c_24707])).
% 18.56/9.59  tff(c_34147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1521, c_34137])).
% 18.56/9.59  tff(c_34282, plain, (![A_140882]: (A_140882='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_33782])).
% 18.56/9.59  tff(c_1438, plain, (![B_78]: (k2_xboole_0('#skF_7', k2_tarski('#skF_6', B_78))=k2_tarski('#skF_6', B_78))), inference(resolution, [status(thm)], [c_193, c_1339])).
% 18.56/9.59  tff(c_23902, plain, (![B_109316]: (r2_hidden('#skF_3'('#skF_7'), k2_xboole_0('#skF_7', B_109316)))), inference(superposition, [status(thm), theory('equality')], [c_23820, c_270])).
% 18.56/9.59  tff(c_23909, plain, (![B_78]: (r2_hidden('#skF_3'('#skF_7'), k2_tarski('#skF_6', B_78)))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_23902])).
% 18.56/9.59  tff(c_33792, plain, (![B_78]: (B_78='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_23909, c_33693])).
% 18.56/9.59  tff(c_34034, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_33792])).
% 18.56/9.59  tff(c_24721, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24665, c_68])).
% 18.56/9.59  tff(c_29595, plain, (r2_hidden('#skF_3'('#skF_3'('#skF_7')), '#skF_6') | '#skF_3'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_29536])).
% 18.56/9.59  tff(c_32067, plain, ('#skF_3'('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_29595])).
% 18.56/9.59  tff(c_32069, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32067, c_29590])).
% 18.56/9.59  tff(c_32098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24721, c_32069])).
% 18.56/9.59  tff(c_32099, plain, (r2_hidden('#skF_3'('#skF_3'('#skF_7')), '#skF_6')), inference(splitRight, [status(thm)], [c_29595])).
% 18.56/9.59  tff(c_34036, plain, (r2_hidden('#skF_3'('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34034, c_32099])).
% 18.56/9.59  tff(c_34308, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34282, c_34036])).
% 18.56/9.59  tff(c_35039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25901, c_34308])).
% 18.56/9.59  tff(c_35042, plain, (![B_149901]: (B_149901='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_33792])).
% 18.56/9.59  tff(c_31493, plain, (![B_137772, C_137773]: (k2_xboole_0('#skF_7', k1_enumset1('#skF_6', B_137772, C_137773))=k1_enumset1('#skF_6', B_137772, C_137773))), inference(resolution, [status(thm)], [c_32, c_1339])).
% 18.56/9.59  tff(c_33399, plain, (![D_139573, B_139574, C_139575]: (~r2_hidden(D_139573, '#skF_7') | r2_hidden(D_139573, k1_enumset1('#skF_6', B_139574, C_139575)))), inference(superposition, [status(thm), theory('equality')], [c_31493, c_6])).
% 18.56/9.59  tff(c_24672, plain, (![C_151]: (r1_tarski(k1_xboole_0, C_151) | ~r2_hidden('#skF_3'('#skF_8'), C_151))), inference(superposition, [status(thm), theory('equality')], [c_24665, c_1092])).
% 18.56/9.59  tff(c_33407, plain, (![B_139574, C_139575]: (r1_tarski(k1_xboole_0, k1_enumset1('#skF_6', B_139574, C_139575)) | ~r2_hidden('#skF_3'('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_33399, c_24672])).
% 18.56/9.59  tff(c_33672, plain, (![B_139574, C_139575]: (r1_tarski(k1_xboole_0, k1_enumset1('#skF_6', B_139574, C_139575)))), inference(demodulation, [status(thm), theory('equality')], [c_24775, c_33407])).
% 18.56/9.59  tff(c_35059, plain, (r1_tarski(k1_xboole_0, '#skF_3'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_35042, c_33672])).
% 18.56/9.59  tff(c_35957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29590, c_35059])).
% 18.56/9.59  tff(c_35958, plain, (r1_tarski(k1_xboole_0, k3_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_25206])).
% 18.56/9.59  tff(c_35963, plain, (k2_xboole_0(k1_xboole_0, k3_tarski('#skF_7'))=k3_tarski('#skF_7')), inference(resolution, [status(thm)], [c_35958, c_22])).
% 18.56/9.59  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.56/9.59  tff(c_1267, plain, (![A_1, B_2]: (r1_tarski('#skF_7', k2_xboole_0(A_1, B_2)) | ~r2_hidden('#skF_6', B_2))), inference(resolution, [status(thm)], [c_4, c_1177])).
% 18.56/9.59  tff(c_37454, plain, (r1_tarski('#skF_7', k3_tarski('#skF_7')) | ~r2_hidden('#skF_6', k3_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_35963, c_1267])).
% 18.56/9.59  tff(c_37474, plain, (~r2_hidden('#skF_6', k3_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_36032, c_37454])).
% 18.56/9.59  tff(c_46811, plain, (![E_210300, B_210301, A_210302]: (E_210300=B_210301 | E_210300=A_210302 | E_210300=A_210302 | ~r2_hidden(E_210300, k2_tarski(A_210302, B_210301)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_46900, plain, (![A_109392]: ('#skF_3'('#skF_8')='#skF_6' | A_109392='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_25848, c_46811])).
% 18.56/9.59  tff(c_47229, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_46900])).
% 18.56/9.59  tff(c_37448, plain, (r2_hidden('#skF_3'('#skF_8'), k3_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_35963, c_24695])).
% 18.56/9.59  tff(c_47235, plain, (r2_hidden('#skF_6', k3_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_47229, c_37448])).
% 18.56/9.59  tff(c_47259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37474, c_47235])).
% 18.56/9.59  tff(c_47583, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_46900])).
% 18.56/9.59  tff(c_47584, plain, (r2_hidden('#skF_6', k3_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_47583, c_37448])).
% 18.56/9.59  tff(c_48193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37474, c_47584])).
% 18.56/9.59  tff(c_48194, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_24664])).
% 18.56/9.59  tff(c_48430, plain, (![C_220687]: (r1_tarski('#skF_7', C_220687) | ~r2_hidden('#skF_3'('#skF_8'), C_220687))), inference(superposition, [status(thm), theory('equality')], [c_48194, c_1092])).
% 18.56/9.59  tff(c_48517, plain, (r1_tarski('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_48430])).
% 18.56/9.59  tff(c_48565, plain, (r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_48517])).
% 18.56/9.59  tff(c_48572, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_48565, c_22])).
% 18.56/9.59  tff(c_48573, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48572, c_513])).
% 18.56/9.59  tff(c_48575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_48573])).
% 18.56/9.59  tff(c_48595, plain, (![B_220688]: (r1_tarski('#skF_7', k1_tarski(B_220688)))), inference(splitRight, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_48598, plain, (![B_220688]: (k1_tarski(B_220688)='#skF_7' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_48595, c_64])).
% 18.56/9.59  tff(c_48606, plain, (![B_220688]: (k1_tarski(B_220688)='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_48598])).
% 18.56/9.59  tff(c_216, plain, (![B_84]: (k2_xboole_0(k1_tarski(B_84), k1_tarski(B_84))=k1_tarski(B_84))), inference(resolution, [status(thm)], [c_66, c_140])).
% 18.56/9.59  tff(c_222, plain, (![B_84]: (k3_tarski(k1_tarski(k1_tarski(B_84)))=k1_tarski(B_84))), inference(superposition, [status(thm), theory('equality')], [c_216, c_117])).
% 18.56/9.59  tff(c_534, plain, (k3_tarski(k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_506, c_222])).
% 18.56/9.59  tff(c_564, plain, (k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_534])).
% 18.56/9.59  tff(c_48615, plain, (k3_tarski('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48606, c_564])).
% 18.56/9.59  tff(c_120, plain, (![A_72]: (k3_tarski(k1_tarski(A_72))=k2_xboole_0(A_72, A_72))), inference(superposition, [status(thm), theory('equality')], [c_50, c_108])).
% 18.56/9.59  tff(c_129, plain, (![A_72]: (r1_tarski(A_72, k3_tarski(k1_tarski(A_72))))), inference(superposition, [status(thm), theory('equality')], [c_120, c_24])).
% 18.56/9.59  tff(c_48629, plain, (![A_72]: (r1_tarski(A_72, k3_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48606, c_129])).
% 18.56/9.59  tff(c_48764, plain, (![A_72]: (r1_tarski(A_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48615, c_48629])).
% 18.56/9.59  tff(c_48875, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48764, c_563])).
% 18.56/9.59  tff(c_48577, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_1106, plain, (![C_151]: (k2_xboole_0('#skF_7', C_151)=C_151 | ~r2_hidden('#skF_6', C_151))), inference(superposition, [status(thm), theory('equality')], [c_506, c_1043])).
% 18.56/9.59  tff(c_48587, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48577, c_1106])).
% 18.56/9.59  tff(c_48876, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_xboole_0 | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_48875, c_48587])).
% 18.56/9.59  tff(c_49062, plain, (k1_xboole_0='#skF_7' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_48876])).
% 18.56/9.59  tff(c_49064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_49062])).
% 18.56/9.59  tff(c_49066, plain, (r2_hidden('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_1255])).
% 18.56/9.59  tff(c_1172, plain, (![C_153]: (r1_tarski('#skF_7', C_153) | ~r2_hidden('#skF_6', C_153))), inference(superposition, [status(thm), theory('equality')], [c_506, c_1155])).
% 18.56/9.59  tff(c_49075, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_49066, c_1172])).
% 18.56/9.59  tff(c_70672, plain, (![A_309186]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_309186, '#skF_6'))=k2_tarski(A_309186, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69289, c_70520])).
% 18.56/9.59  tff(c_70677, plain, (![A_309186]: (r2_hidden('#skF_3'('#skF_8'), k2_tarski(A_309186, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_70672, c_69152])).
% 18.56/9.59  tff(c_77778, plain, (![E_341145, B_341146, A_341147]: (E_341145=B_341146 | E_341145=A_341147 | E_341145=A_341147 | ~r2_hidden(E_341145, k2_tarski(A_341147, B_341146)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_77867, plain, (![A_309186]: ('#skF_3'('#skF_8')='#skF_6' | A_309186='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_70677, c_77778])).
% 18.56/9.59  tff(c_77963, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_77867])).
% 18.56/9.59  tff(c_1263, plain, (![A_20]: (r1_tarski('#skF_7', k3_tarski(k1_tarski(A_20))) | ~r2_hidden('#skF_6', A_20))), inference(resolution, [status(thm)], [c_339, c_1177])).
% 18.56/9.59  tff(c_69126, plain, (r1_tarski('#skF_7', k3_tarski(k1_xboole_0)) | ~r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_69122, c_1263])).
% 18.56/9.59  tff(c_70666, plain, (~r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(splitLeft, [status(thm)], [c_69126])).
% 18.56/9.59  tff(c_70671, plain, (~r1_tarski('#skF_7', '#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_528, c_70666])).
% 18.56/9.59  tff(c_77970, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_77963, c_70671])).
% 18.56/9.59  tff(c_77995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49075, c_77970])).
% 18.56/9.59  tff(c_77997, plain, ('#skF_3'('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_77867])).
% 18.56/9.59  tff(c_78130, plain, (![A_342287]: (A_342287='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_77867])).
% 18.56/9.59  tff(c_49661, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_49647])).
% 18.56/9.59  tff(c_49672, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_49661])).
% 18.56/9.59  tff(c_49673, plain, (k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_49672])).
% 18.56/9.59  tff(c_49715, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49673, c_208])).
% 18.56/9.59  tff(c_49793, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_49715, c_525])).
% 18.56/9.59  tff(c_49235, plain, (![B_223686]: (k2_xboole_0('#skF_7', k2_tarski('#skF_6', B_223686))=k2_tarski('#skF_6', B_223686))), inference(resolution, [status(thm)], [c_193, c_1339])).
% 18.56/9.59  tff(c_49249, plain, (![D_6, B_223686]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, k2_tarski('#skF_6', B_223686)))), inference(superposition, [status(thm), theory('equality')], [c_49235, c_6])).
% 18.56/9.59  tff(c_59323, plain, (![C_265730]: (k2_xboole_0(k1_xboole_0, C_265730)=C_265730 | ~r2_hidden('#skF_3'('#skF_7'), C_265730))), inference(superposition, [status(thm), theory('equality')], [c_49673, c_1042])).
% 18.56/9.59  tff(c_59353, plain, (![B_223686]: (k2_xboole_0(k1_xboole_0, k2_tarski('#skF_6', B_223686))=k2_tarski('#skF_6', B_223686) | ~r2_hidden('#skF_3'('#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_49249, c_59323])).
% 18.56/9.59  tff(c_65990, plain, (![B_296237]: (k2_xboole_0(k1_xboole_0, k2_tarski('#skF_6', B_296237))=k2_tarski('#skF_6', B_296237))), inference(demodulation, [status(thm), theory('equality')], [c_49793, c_59353])).
% 18.56/9.59  tff(c_49703, plain, (![B_91]: (r2_hidden('#skF_3'('#skF_7'), k2_xboole_0(k1_xboole_0, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_49673, c_270])).
% 18.56/9.59  tff(c_66001, plain, (![B_296237]: (r2_hidden('#skF_3'('#skF_7'), k2_tarski('#skF_6', B_296237)))), inference(superposition, [status(thm), theory('equality')], [c_65990, c_49703])).
% 18.56/9.59  tff(c_66994, plain, (![E_298037, B_298038, A_298039]: (E_298037=B_298038 | E_298037=A_298039 | E_298037=A_298039 | ~r2_hidden(E_298037, k2_tarski(A_298039, B_298038)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_67075, plain, (![B_296237]: (B_296237='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_66001, c_66994])).
% 18.56/9.59  tff(c_67095, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_67075])).
% 18.56/9.59  tff(c_67128, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67095, c_49715])).
% 18.56/9.59  tff(c_67146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49067, c_67128])).
% 18.56/9.59  tff(c_67654, plain, ('#skF_3'('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_67075])).
% 18.56/9.59  tff(c_50535, plain, (![C_223743]: (k2_xboole_0(k1_xboole_0, C_223743)=C_223743 | ~r2_hidden('#skF_3'('#skF_7'), C_223743))), inference(superposition, [status(thm), theory('equality')], [c_49673, c_1042])).
% 18.56/9.59  tff(c_50565, plain, (![A_223691]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_223691, '#skF_6'))=k2_tarski(A_223691, '#skF_6') | ~r2_hidden('#skF_3'('#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_49351, c_50535])).
% 18.56/9.59  tff(c_53543, plain, (![A_233128]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_233128, '#skF_6'))=k2_tarski(A_233128, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_49793, c_50565])).
% 18.56/9.59  tff(c_53554, plain, (![A_233128]: (r2_hidden('#skF_3'('#skF_7'), k2_tarski(A_233128, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_53543, c_49703])).
% 18.56/9.59  tff(c_58063, plain, (![E_254596, B_254597, A_254598]: (E_254596=B_254597 | E_254596=A_254598 | E_254596=A_254598 | ~r2_hidden(E_254596, k2_tarski(A_254598, B_254597)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_992])).
% 18.56/9.59  tff(c_58152, plain, (![A_233128]: ('#skF_3'('#skF_7')='#skF_6' | A_233128='#skF_3'('#skF_7'))), inference(resolution, [status(thm)], [c_53554, c_58063])).
% 18.56/9.59  tff(c_58172, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_58152])).
% 18.56/9.59  tff(c_49677, plain, (r1_tarski('#skF_7', k3_tarski(k1_xboole_0)) | ~r2_hidden('#skF_6', '#skF_3'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_49673, c_1263])).
% 18.56/9.59  tff(c_50482, plain, (~r2_hidden('#skF_6', '#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_49677])).
% 18.56/9.59  tff(c_50486, plain, (~r1_tarski('#skF_7', '#skF_3'('#skF_7'))), inference(resolution, [status(thm)], [c_528, c_50482])).
% 18.56/9.59  tff(c_58181, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58172, c_50486])).
% 18.56/9.59  tff(c_58204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49075, c_58181])).
% 18.56/9.59  tff(c_58206, plain, ('#skF_3'('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_58152])).
% 18.56/9.59  tff(c_58224, plain, (![A_255087]: (A_255087='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_58152])).
% 18.56/9.59  tff(c_49074, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_49066, c_1106])).
% 18.56/9.59  tff(c_49155, plain, (![D_223680]: (~r2_hidden(D_223680, '#skF_7') | r2_hidden(D_223680, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49074, c_6])).
% 18.56/9.59  tff(c_49169, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_49155])).
% 18.56/9.59  tff(c_49178, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_49169])).
% 18.56/9.59  tff(c_50006, plain, (![C_223721]: (r1_tarski(k1_xboole_0, C_223721) | ~r2_hidden('#skF_3'('#skF_7'), C_223721))), inference(superposition, [status(thm), theory('equality')], [c_49673, c_1092])).
% 18.56/9.59  tff(c_50132, plain, (r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_49178, c_50006])).
% 18.56/9.59  tff(c_50163, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_50132, c_22])).
% 18.56/9.59  tff(c_58733, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_58224, c_50163])).
% 18.56/9.59  tff(c_59171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58206, c_58733])).
% 18.56/9.59  tff(c_59173, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_49677])).
% 18.56/9.59  tff(c_59185, plain, (r1_tarski('#skF_7', '#skF_3'('#skF_7'))), inference(resolution, [status(thm)], [c_59173, c_1172])).
% 18.56/9.59  tff(c_67655, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67654, c_59185])).
% 18.56/9.59  tff(c_68275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49079, c_67655])).
% 18.56/9.59  tff(c_68276, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_49672])).
% 18.56/9.59  tff(c_68364, plain, (![B_309111]: (r2_hidden('#skF_3'('#skF_7'), k2_xboole_0('#skF_7', B_309111)))), inference(superposition, [status(thm), theory('equality')], [c_68276, c_270])).
% 18.56/9.59  tff(c_68371, plain, (![B_78]: (r2_hidden('#skF_3'('#skF_7'), k2_tarski('#skF_6', B_78)))), inference(superposition, [status(thm), theory('equality')], [c_1438, c_68364])).
% 18.56/9.59  tff(c_77877, plain, (![B_78]: (B_78='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_68371, c_77778])).
% 18.56/9.59  tff(c_77887, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_77877])).
% 18.56/9.59  tff(c_78166, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_78130, c_77887])).
% 18.56/9.59  tff(c_78930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77997, c_78166])).
% 18.56/9.59  tff(c_78932, plain, ('#skF_3'('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_77877])).
% 18.56/9.59  tff(c_78933, plain, (![B_351954]: (B_351954='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_77877])).
% 18.56/9.59  tff(c_49108, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49074, c_6])).
% 18.56/9.59  tff(c_69300, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_69289, c_49108])).
% 18.56/9.59  tff(c_69406, plain, (![C_309158]: (r1_tarski(k1_xboole_0, C_309158) | ~r2_hidden('#skF_3'('#skF_8'), C_309158))), inference(superposition, [status(thm), theory('equality')], [c_69122, c_1092])).
% 18.56/9.59  tff(c_69518, plain, (r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_69300, c_69406])).
% 18.56/9.59  tff(c_69568, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_69518, c_22])).
% 18.56/9.59  tff(c_79210, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_78933, c_69568])).
% 18.56/9.59  tff(c_79891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78932, c_79210])).
% 18.56/9.59  tff(c_79893, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_69126])).
% 18.56/9.59  tff(c_79922, plain, (r1_tarski('#skF_7', '#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_79893, c_1172])).
% 18.56/9.59  tff(c_87481, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87480, c_79922])).
% 18.56/9.59  tff(c_88123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49079, c_87481])).
% 18.56/9.59  tff(c_88124, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_69121])).
% 18.56/9.59  tff(c_88350, plain, (![C_404764]: (r1_tarski('#skF_7', C_404764) | ~r2_hidden('#skF_3'('#skF_8'), C_404764))), inference(superposition, [status(thm), theory('equality')], [c_88124, c_1092])).
% 18.56/9.59  tff(c_88448, plain, (r1_tarski('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_88350])).
% 18.56/9.59  tff(c_88507, plain, (r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_88448])).
% 18.56/9.59  tff(c_88570, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88507, c_22])).
% 18.56/9.59  tff(c_88571, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88570, c_513])).
% 18.56/9.59  tff(c_88573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_88571])).
% 18.56/9.59  tff(c_88605, plain, (![B_404769]: (r1_tarski('#skF_7', k1_tarski(B_404769)))), inference(splitRight, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_88608, plain, (![B_404769]: (k1_tarski(B_404769)='#skF_7' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_88605, c_64])).
% 18.56/9.59  tff(c_88616, plain, (![B_404769]: (k1_tarski(B_404769)='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_88608])).
% 18.56/9.59  tff(c_88625, plain, (k3_tarski('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88616, c_564])).
% 18.56/9.59  tff(c_88639, plain, (![A_72]: (r1_tarski(A_72, k3_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88616, c_129])).
% 18.56/9.59  tff(c_88917, plain, (![A_72]: (r1_tarski(A_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88625, c_88639])).
% 18.56/9.59  tff(c_88981, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88917, c_563])).
% 18.56/9.59  tff(c_88575, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1264])).
% 18.56/9.59  tff(c_88597, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_88575, c_1106])).
% 18.56/9.59  tff(c_88982, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_xboole_0 | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_88981, c_88597])).
% 18.56/9.59  tff(c_89169, plain, (k1_xboole_0='#skF_7' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_88982])).
% 18.56/9.59  tff(c_89171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_89169])).
% 18.56/9.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.56/9.59  
% 18.56/9.59  Inference rules
% 18.56/9.59  ----------------------
% 18.56/9.59  #Ref     : 0
% 18.56/9.59  #Sup     : 13314
% 18.56/9.59  #Fact    : 194
% 18.56/9.59  #Define  : 0
% 18.56/9.59  #Split   : 53
% 18.56/9.59  #Chain   : 0
% 18.56/9.59  #Close   : 0
% 18.56/9.59  
% 18.56/9.59  Ordering : KBO
% 18.56/9.59  
% 18.56/9.59  Simplification rules
% 18.56/9.59  ----------------------
% 18.56/9.59  #Subsume      : 1319
% 18.56/9.59  #Demod        : 5526
% 18.56/9.59  #Tautology    : 3980
% 18.56/9.59  #SimpNegUnit  : 468
% 18.56/9.59  #BackRed      : 737
% 18.56/9.59  
% 18.56/9.59  #Partial instantiations: 109545
% 18.56/9.59  #Strategies tried      : 1
% 18.56/9.59  
% 18.56/9.59  Timing (in seconds)
% 18.56/9.59  ----------------------
% 18.56/9.60  Preprocessing        : 0.34
% 18.56/9.60  Parsing              : 0.17
% 18.56/9.60  CNF conversion       : 0.03
% 18.56/9.60  Main loop            : 8.42
% 18.56/9.60  Inferencing          : 4.17
% 18.56/9.60  Reduction            : 2.58
% 18.56/9.60  Demodulation         : 2.09
% 18.56/9.60  BG Simplification    : 0.23
% 18.56/9.60  Subsumption          : 1.10
% 18.56/9.60  Abstraction          : 0.29
% 18.56/9.60  MUC search           : 0.00
% 18.56/9.60  Cooper               : 0.00
% 18.56/9.60  Total                : 8.87
% 18.56/9.60  Index Insertion      : 0.00
% 18.56/9.60  Index Deletion       : 0.00
% 18.56/9.60  Index Matching       : 0.00
% 18.56/9.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
