%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:36 EST 2020

% Result     : Theorem 13.41s
% Output     : CNFRefutation 13.71s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 166 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 296 expanded)
%              Number of equality atoms :   46 ( 109 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > #skF_11 > #skF_6 > #skF_4 > #skF_8 > #skF_12 > #skF_2 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] : k1_wellord2(k1_tarski(A)) = k1_tarski(k4_tarski(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).

tff(c_32,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_98,B_99] : k1_enumset1(A_98,A_98,B_99) = k2_tarski(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [E_9,A_3,C_5] : r2_hidden(E_9,k1_enumset1(A_3,E_9,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_160,plain,(
    ! [A_103,B_104] : r2_hidden(A_103,k2_tarski(A_103,B_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_12])).

tff(c_163,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_160])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_84] : v1_relat_1(k1_wellord2(A_84)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_96,plain,(
    ! [C_82,D_83,A_76] :
      ( r2_hidden(k4_tarski(C_82,D_83),k1_wellord2(A_76))
      | ~ r1_tarski(C_82,D_83)
      | ~ r2_hidden(D_83,A_76)
      | ~ r2_hidden(C_82,A_76)
      | ~ v1_relat_1(k1_wellord2(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    ! [C_82,D_83,A_76] :
      ( r2_hidden(k4_tarski(C_82,D_83),k1_wellord2(A_76))
      | ~ r1_tarski(C_82,D_83)
      | ~ r2_hidden(D_83,A_76)
      | ~ r2_hidden(C_82,A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96])).

tff(c_359,plain,(
    ! [A_142,B_143,C_144] : k2_zfmisc_1(k2_tarski(A_142,B_143),k1_tarski(C_144)) = k2_tarski(k4_tarski(A_142,C_144),k4_tarski(B_143,C_144)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_390,plain,(
    ! [B_143,C_144] : k2_zfmisc_1(k2_tarski(B_143,B_143),k1_tarski(C_144)) = k1_tarski(k4_tarski(B_143,C_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_32])).

tff(c_409,plain,(
    ! [B_143,C_144] : k2_zfmisc_1(k1_tarski(B_143),k1_tarski(C_144)) = k1_tarski(k4_tarski(B_143,C_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_390])).

tff(c_94,plain,(
    ! [A_76] :
      ( k3_relat_1(k1_wellord2(A_76)) = A_76
      | ~ v1_relat_1(k1_wellord2(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_108,plain,(
    ! [A_76] : k3_relat_1(k1_wellord2(A_76)) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_94])).

tff(c_792,plain,(
    ! [A_196,B_197] :
      ( r2_hidden(k4_tarski('#skF_9'(A_196,B_197),'#skF_10'(A_196,B_197)),A_196)
      | r1_tarski(A_196,B_197)
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_78,plain,(
    ! [B_74,C_75,A_73] :
      ( r2_hidden(B_74,k3_relat_1(C_75))
      | ~ r2_hidden(k4_tarski(A_73,B_74),C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_852,plain,(
    ! [A_202,B_203] :
      ( r2_hidden('#skF_10'(A_202,B_203),k3_relat_1(A_202))
      | r1_tarski(A_202,B_203)
      | ~ v1_relat_1(A_202) ) ),
    inference(resolution,[status(thm)],[c_792,c_78])).

tff(c_855,plain,(
    ! [A_76,B_203] :
      ( r2_hidden('#skF_10'(k1_wellord2(A_76),B_203),A_76)
      | r1_tarski(k1_wellord2(A_76),B_203)
      | ~ v1_relat_1(k1_wellord2(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_852])).

tff(c_857,plain,(
    ! [A_76,B_203] :
      ( r2_hidden('#skF_10'(k1_wellord2(A_76),B_203),A_76)
      | r1_tarski(k1_wellord2(A_76),B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_855])).

tff(c_10,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,(
    ! [B_99,A_98] : r2_hidden(B_99,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_10])).

tff(c_236,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(k2_tarski(A_121,B_122),C_123)
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,(
    ! [A_10,C_123] :
      ( r1_tarski(k1_tarski(A_10),C_123)
      | ~ r2_hidden(A_10,C_123)
      | ~ r2_hidden(A_10,C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1086,plain,(
    ! [A_232,B_233,C_234] :
      ( k2_tarski(A_232,B_233) = C_234
      | ~ r1_tarski(C_234,k2_tarski(A_232,B_233))
      | ~ r2_hidden(B_233,C_234)
      | ~ r2_hidden(A_232,C_234) ) ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_5853,plain,(
    ! [A_571,B_572,A_573] :
      ( k2_tarski(A_571,B_572) = k1_tarski(A_573)
      | ~ r2_hidden(B_572,k1_tarski(A_573))
      | ~ r2_hidden(A_571,k1_tarski(A_573))
      | ~ r2_hidden(A_573,k2_tarski(A_571,B_572)) ) ),
    inference(resolution,[status(thm)],[c_247,c_1086])).

tff(c_5905,plain,(
    ! [A_571,A_10] :
      ( k2_tarski(A_571,A_10) = k1_tarski(A_10)
      | ~ r2_hidden(A_571,k1_tarski(A_10))
      | ~ r2_hidden(A_10,k2_tarski(A_571,A_10)) ) ),
    inference(resolution,[status(thm)],[c_163,c_5853])).

tff(c_5926,plain,(
    ! [A_574,A_575] :
      ( k2_tarski(A_574,A_575) = k1_tarski(A_575)
      | ~ r2_hidden(A_574,k1_tarski(A_575)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_5905])).

tff(c_6049,plain,(
    ! [A_581,B_582] :
      ( k2_tarski('#skF_10'(k1_wellord2(k1_tarski(A_581)),B_582),A_581) = k1_tarski(A_581)
      | r1_tarski(k1_wellord2(k1_tarski(A_581)),B_582) ) ),
    inference(resolution,[status(thm)],[c_857,c_5926])).

tff(c_494,plain,(
    ! [A_158,B_159,C_160] : k2_zfmisc_1(k1_tarski(A_158),k2_tarski(B_159,C_160)) = k2_tarski(k4_tarski(A_158,B_159),k4_tarski(A_158,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_139,plain,(
    ! [A_98,B_99] : r2_hidden(A_98,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_12])).

tff(c_531,plain,(
    ! [A_158,B_159,C_160] : r2_hidden(k4_tarski(A_158,B_159),k2_zfmisc_1(k1_tarski(A_158),k2_tarski(B_159,C_160))) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_139])).

tff(c_6156,plain,(
    ! [A_158,A_581,B_582] :
      ( r2_hidden(k4_tarski(A_158,'#skF_10'(k1_wellord2(k1_tarski(A_581)),B_582)),k2_zfmisc_1(k1_tarski(A_158),k1_tarski(A_581)))
      | r1_tarski(k1_wellord2(k1_tarski(A_581)),B_582) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6049,c_531])).

tff(c_7346,plain,(
    ! [A_633,A_634,B_635] :
      ( r2_hidden(k4_tarski(A_633,'#skF_10'(k1_wellord2(k1_tarski(A_634)),B_635)),k1_tarski(k4_tarski(A_633,A_634)))
      | r1_tarski(k1_wellord2(k1_tarski(A_634)),B_635) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_6156])).

tff(c_80,plain,(
    ! [A_73,C_75,B_74] :
      ( r2_hidden(A_73,k3_relat_1(C_75))
      | ~ r2_hidden(k4_tarski(A_73,B_74),C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_826,plain,(
    ! [A_198,B_199] :
      ( r2_hidden('#skF_9'(A_198,B_199),k3_relat_1(A_198))
      | r1_tarski(A_198,B_199)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_792,c_80])).

tff(c_829,plain,(
    ! [A_76,B_199] :
      ( r2_hidden('#skF_9'(k1_wellord2(A_76),B_199),A_76)
      | r1_tarski(k1_wellord2(A_76),B_199)
      | ~ v1_relat_1(k1_wellord2(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_826])).

tff(c_831,plain,(
    ! [A_76,B_199] :
      ( r2_hidden('#skF_9'(k1_wellord2(A_76),B_199),A_76)
      | r1_tarski(k1_wellord2(A_76),B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_829])).

tff(c_628,plain,(
    ! [E_168,F_169,A_170,B_171] :
      ( r2_hidden(k4_tarski(E_168,F_169),k2_zfmisc_1(A_170,B_171))
      | ~ r2_hidden(F_169,B_171)
      | ~ r2_hidden(E_168,A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1982,plain,(
    ! [E_330,F_331,B_332,C_333] :
      ( r2_hidden(k4_tarski(E_330,F_331),k1_tarski(k4_tarski(B_332,C_333)))
      | ~ r2_hidden(F_331,k1_tarski(C_333))
      | ~ r2_hidden(E_330,k1_tarski(B_332)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_628])).

tff(c_34,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_309,plain,(
    ! [E_131,C_132,B_133,A_134] :
      ( E_131 = C_132
      | E_131 = B_133
      | E_131 = A_134
      | ~ r2_hidden(E_131,k1_enumset1(A_134,B_133,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_328,plain,(
    ! [E_135,B_136,A_137] :
      ( E_135 = B_136
      | E_135 = A_137
      | E_135 = A_137
      | ~ r2_hidden(E_135,k2_tarski(A_137,B_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_309])).

tff(c_337,plain,(
    ! [E_135,A_10] :
      ( E_135 = A_10
      | E_135 = A_10
      | E_135 = A_10
      | ~ r2_hidden(E_135,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_328])).

tff(c_2012,plain,(
    ! [E_334,F_335,B_336,C_337] :
      ( k4_tarski(E_334,F_335) = k4_tarski(B_336,C_337)
      | ~ r2_hidden(F_335,k1_tarski(C_337))
      | ~ r2_hidden(E_334,k1_tarski(B_336)) ) ),
    inference(resolution,[status(thm)],[c_1982,c_337])).

tff(c_2059,plain,(
    ! [E_338,A_339,B_340] :
      ( k4_tarski(E_338,A_339) = k4_tarski(B_340,A_339)
      | ~ r2_hidden(E_338,k1_tarski(B_340)) ) ),
    inference(resolution,[status(thm)],[c_163,c_2012])).

tff(c_2273,plain,(
    ! [B_348,B_349,A_350] :
      ( k4_tarski('#skF_9'(k1_wellord2(k1_tarski(B_348)),B_349),A_350) = k4_tarski(B_348,A_350)
      | r1_tarski(k1_wellord2(k1_tarski(B_348)),B_349) ) ),
    inference(resolution,[status(thm)],[c_831,c_2059])).

tff(c_74,plain,(
    ! [A_56,B_66] :
      ( ~ r2_hidden(k4_tarski('#skF_9'(A_56,B_66),'#skF_10'(A_56,B_66)),B_66)
      | r1_tarski(A_56,B_66)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2368,plain,(
    ! [B_348,B_349] :
      ( ~ r2_hidden(k4_tarski(B_348,'#skF_10'(k1_wellord2(k1_tarski(B_348)),B_349)),B_349)
      | r1_tarski(k1_wellord2(k1_tarski(B_348)),B_349)
      | ~ v1_relat_1(k1_wellord2(k1_tarski(B_348)))
      | r1_tarski(k1_wellord2(k1_tarski(B_348)),B_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2273,c_74])).

tff(c_2415,plain,(
    ! [B_348,B_349] :
      ( ~ r2_hidden(k4_tarski(B_348,'#skF_10'(k1_wellord2(k1_tarski(B_348)),B_349)),B_349)
      | r1_tarski(k1_wellord2(k1_tarski(B_348)),B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2368])).

tff(c_7425,plain,(
    ! [A_636] : r1_tarski(k1_wellord2(k1_tarski(A_636)),k1_tarski(k4_tarski(A_636,A_636))) ),
    inference(resolution,[status(thm)],[c_7346,c_2415])).

tff(c_251,plain,(
    ! [A_124,C_125] :
      ( r1_tarski(k1_tarski(A_124),C_125)
      | ~ r2_hidden(A_124,C_125)
      | ~ r2_hidden(A_124,C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_257,plain,(
    ! [A_124,C_125] :
      ( k1_tarski(A_124) = C_125
      | ~ r1_tarski(C_125,k1_tarski(A_124))
      | ~ r2_hidden(A_124,C_125) ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_7453,plain,(
    ! [A_637] :
      ( k1_wellord2(k1_tarski(A_637)) = k1_tarski(k4_tarski(A_637,A_637))
      | ~ r2_hidden(k4_tarski(A_637,A_637),k1_wellord2(k1_tarski(A_637))) ) ),
    inference(resolution,[status(thm)],[c_7425,c_257])).

tff(c_7469,plain,(
    ! [D_83] :
      ( k1_wellord2(k1_tarski(D_83)) = k1_tarski(k4_tarski(D_83,D_83))
      | ~ r1_tarski(D_83,D_83)
      | ~ r2_hidden(D_83,k1_tarski(D_83)) ) ),
    inference(resolution,[status(thm)],[c_106,c_7453])).

tff(c_7472,plain,(
    ! [D_83] : k1_wellord2(k1_tarski(D_83)) = k1_tarski(k4_tarski(D_83,D_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_6,c_7469])).

tff(c_102,plain,(
    k1_wellord2(k1_tarski('#skF_13')) != k1_tarski(k4_tarski('#skF_13','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7472,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.41/4.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.41/4.56  
% 13.41/4.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.41/4.56  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > #skF_11 > #skF_6 > #skF_4 > #skF_8 > #skF_12 > #skF_2 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_1 > #skF_9
% 13.41/4.56  
% 13.41/4.56  %Foreground sorts:
% 13.41/4.56  
% 13.41/4.56  
% 13.41/4.56  %Background operators:
% 13.41/4.56  
% 13.41/4.56  
% 13.41/4.56  %Foreground operators:
% 13.41/4.56  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 13.41/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.41/4.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.41/4.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 13.41/4.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.41/4.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.41/4.56  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 13.41/4.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.41/4.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.41/4.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.41/4.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 13.41/4.56  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 13.41/4.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.41/4.56  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 13.41/4.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.41/4.56  tff('#skF_13', type, '#skF_13': $i).
% 13.41/4.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.41/4.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.41/4.56  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 13.41/4.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 13.41/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.41/4.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.41/4.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.41/4.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.41/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.41/4.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 13.41/4.56  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 13.41/4.56  
% 13.71/4.59  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.71/4.59  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.71/4.59  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 13.71/4.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.71/4.59  tff(f_109, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 13.71/4.59  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 13.71/4.59  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 13.71/4.59  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 13.71/4.59  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 13.71/4.59  tff(f_74, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 13.71/4.59  tff(f_64, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 13.71/4.59  tff(f_112, negated_conjecture, ~(![A]: (k1_wellord2(k1_tarski(A)) = k1_tarski(k4_tarski(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord2)).
% 13.71/4.59  tff(c_32, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.71/4.59  tff(c_133, plain, (![A_98, B_99]: (k1_enumset1(A_98, A_98, B_99)=k2_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.71/4.59  tff(c_12, plain, (![E_9, A_3, C_5]: (r2_hidden(E_9, k1_enumset1(A_3, E_9, C_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.71/4.59  tff(c_160, plain, (![A_103, B_104]: (r2_hidden(A_103, k2_tarski(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_12])).
% 13.71/4.59  tff(c_163, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_160])).
% 13.71/4.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.71/4.59  tff(c_100, plain, (![A_84]: (v1_relat_1(k1_wellord2(A_84)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.71/4.59  tff(c_96, plain, (![C_82, D_83, A_76]: (r2_hidden(k4_tarski(C_82, D_83), k1_wellord2(A_76)) | ~r1_tarski(C_82, D_83) | ~r2_hidden(D_83, A_76) | ~r2_hidden(C_82, A_76) | ~v1_relat_1(k1_wellord2(A_76)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.71/4.59  tff(c_106, plain, (![C_82, D_83, A_76]: (r2_hidden(k4_tarski(C_82, D_83), k1_wellord2(A_76)) | ~r1_tarski(C_82, D_83) | ~r2_hidden(D_83, A_76) | ~r2_hidden(C_82, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96])).
% 13.71/4.59  tff(c_359, plain, (![A_142, B_143, C_144]: (k2_zfmisc_1(k2_tarski(A_142, B_143), k1_tarski(C_144))=k2_tarski(k4_tarski(A_142, C_144), k4_tarski(B_143, C_144)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.71/4.59  tff(c_390, plain, (![B_143, C_144]: (k2_zfmisc_1(k2_tarski(B_143, B_143), k1_tarski(C_144))=k1_tarski(k4_tarski(B_143, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_359, c_32])).
% 13.71/4.59  tff(c_409, plain, (![B_143, C_144]: (k2_zfmisc_1(k1_tarski(B_143), k1_tarski(C_144))=k1_tarski(k4_tarski(B_143, C_144)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_390])).
% 13.71/4.59  tff(c_94, plain, (![A_76]: (k3_relat_1(k1_wellord2(A_76))=A_76 | ~v1_relat_1(k1_wellord2(A_76)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.71/4.59  tff(c_108, plain, (![A_76]: (k3_relat_1(k1_wellord2(A_76))=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_94])).
% 13.71/4.59  tff(c_792, plain, (![A_196, B_197]: (r2_hidden(k4_tarski('#skF_9'(A_196, B_197), '#skF_10'(A_196, B_197)), A_196) | r1_tarski(A_196, B_197) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.71/4.59  tff(c_78, plain, (![B_74, C_75, A_73]: (r2_hidden(B_74, k3_relat_1(C_75)) | ~r2_hidden(k4_tarski(A_73, B_74), C_75) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.71/4.59  tff(c_852, plain, (![A_202, B_203]: (r2_hidden('#skF_10'(A_202, B_203), k3_relat_1(A_202)) | r1_tarski(A_202, B_203) | ~v1_relat_1(A_202))), inference(resolution, [status(thm)], [c_792, c_78])).
% 13.71/4.59  tff(c_855, plain, (![A_76, B_203]: (r2_hidden('#skF_10'(k1_wellord2(A_76), B_203), A_76) | r1_tarski(k1_wellord2(A_76), B_203) | ~v1_relat_1(k1_wellord2(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_852])).
% 13.71/4.59  tff(c_857, plain, (![A_76, B_203]: (r2_hidden('#skF_10'(k1_wellord2(A_76), B_203), A_76) | r1_tarski(k1_wellord2(A_76), B_203))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_855])).
% 13.71/4.59  tff(c_10, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.71/4.59  tff(c_142, plain, (![B_99, A_98]: (r2_hidden(B_99, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_10])).
% 13.71/4.59  tff(c_236, plain, (![A_121, B_122, C_123]: (r1_tarski(k2_tarski(A_121, B_122), C_123) | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.71/4.59  tff(c_247, plain, (![A_10, C_123]: (r1_tarski(k1_tarski(A_10), C_123) | ~r2_hidden(A_10, C_123) | ~r2_hidden(A_10, C_123))), inference(superposition, [status(thm), theory('equality')], [c_32, c_236])).
% 13.71/4.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.71/4.59  tff(c_1086, plain, (![A_232, B_233, C_234]: (k2_tarski(A_232, B_233)=C_234 | ~r1_tarski(C_234, k2_tarski(A_232, B_233)) | ~r2_hidden(B_233, C_234) | ~r2_hidden(A_232, C_234))), inference(resolution, [status(thm)], [c_236, c_2])).
% 13.71/4.59  tff(c_5853, plain, (![A_571, B_572, A_573]: (k2_tarski(A_571, B_572)=k1_tarski(A_573) | ~r2_hidden(B_572, k1_tarski(A_573)) | ~r2_hidden(A_571, k1_tarski(A_573)) | ~r2_hidden(A_573, k2_tarski(A_571, B_572)))), inference(resolution, [status(thm)], [c_247, c_1086])).
% 13.71/4.59  tff(c_5905, plain, (![A_571, A_10]: (k2_tarski(A_571, A_10)=k1_tarski(A_10) | ~r2_hidden(A_571, k1_tarski(A_10)) | ~r2_hidden(A_10, k2_tarski(A_571, A_10)))), inference(resolution, [status(thm)], [c_163, c_5853])).
% 13.71/4.59  tff(c_5926, plain, (![A_574, A_575]: (k2_tarski(A_574, A_575)=k1_tarski(A_575) | ~r2_hidden(A_574, k1_tarski(A_575)))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_5905])).
% 13.71/4.59  tff(c_6049, plain, (![A_581, B_582]: (k2_tarski('#skF_10'(k1_wellord2(k1_tarski(A_581)), B_582), A_581)=k1_tarski(A_581) | r1_tarski(k1_wellord2(k1_tarski(A_581)), B_582))), inference(resolution, [status(thm)], [c_857, c_5926])).
% 13.71/4.59  tff(c_494, plain, (![A_158, B_159, C_160]: (k2_zfmisc_1(k1_tarski(A_158), k2_tarski(B_159, C_160))=k2_tarski(k4_tarski(A_158, B_159), k4_tarski(A_158, C_160)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.71/4.59  tff(c_139, plain, (![A_98, B_99]: (r2_hidden(A_98, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_12])).
% 13.71/4.59  tff(c_531, plain, (![A_158, B_159, C_160]: (r2_hidden(k4_tarski(A_158, B_159), k2_zfmisc_1(k1_tarski(A_158), k2_tarski(B_159, C_160))))), inference(superposition, [status(thm), theory('equality')], [c_494, c_139])).
% 13.71/4.59  tff(c_6156, plain, (![A_158, A_581, B_582]: (r2_hidden(k4_tarski(A_158, '#skF_10'(k1_wellord2(k1_tarski(A_581)), B_582)), k2_zfmisc_1(k1_tarski(A_158), k1_tarski(A_581))) | r1_tarski(k1_wellord2(k1_tarski(A_581)), B_582))), inference(superposition, [status(thm), theory('equality')], [c_6049, c_531])).
% 13.71/4.59  tff(c_7346, plain, (![A_633, A_634, B_635]: (r2_hidden(k4_tarski(A_633, '#skF_10'(k1_wellord2(k1_tarski(A_634)), B_635)), k1_tarski(k4_tarski(A_633, A_634))) | r1_tarski(k1_wellord2(k1_tarski(A_634)), B_635))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_6156])).
% 13.71/4.59  tff(c_80, plain, (![A_73, C_75, B_74]: (r2_hidden(A_73, k3_relat_1(C_75)) | ~r2_hidden(k4_tarski(A_73, B_74), C_75) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.71/4.59  tff(c_826, plain, (![A_198, B_199]: (r2_hidden('#skF_9'(A_198, B_199), k3_relat_1(A_198)) | r1_tarski(A_198, B_199) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_792, c_80])).
% 13.71/4.59  tff(c_829, plain, (![A_76, B_199]: (r2_hidden('#skF_9'(k1_wellord2(A_76), B_199), A_76) | r1_tarski(k1_wellord2(A_76), B_199) | ~v1_relat_1(k1_wellord2(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_826])).
% 13.71/4.59  tff(c_831, plain, (![A_76, B_199]: (r2_hidden('#skF_9'(k1_wellord2(A_76), B_199), A_76) | r1_tarski(k1_wellord2(A_76), B_199))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_829])).
% 13.71/4.59  tff(c_628, plain, (![E_168, F_169, A_170, B_171]: (r2_hidden(k4_tarski(E_168, F_169), k2_zfmisc_1(A_170, B_171)) | ~r2_hidden(F_169, B_171) | ~r2_hidden(E_168, A_170))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.71/4.59  tff(c_1982, plain, (![E_330, F_331, B_332, C_333]: (r2_hidden(k4_tarski(E_330, F_331), k1_tarski(k4_tarski(B_332, C_333))) | ~r2_hidden(F_331, k1_tarski(C_333)) | ~r2_hidden(E_330, k1_tarski(B_332)))), inference(superposition, [status(thm), theory('equality')], [c_409, c_628])).
% 13.71/4.59  tff(c_34, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.71/4.59  tff(c_309, plain, (![E_131, C_132, B_133, A_134]: (E_131=C_132 | E_131=B_133 | E_131=A_134 | ~r2_hidden(E_131, k1_enumset1(A_134, B_133, C_132)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.71/4.59  tff(c_328, plain, (![E_135, B_136, A_137]: (E_135=B_136 | E_135=A_137 | E_135=A_137 | ~r2_hidden(E_135, k2_tarski(A_137, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_309])).
% 13.71/4.59  tff(c_337, plain, (![E_135, A_10]: (E_135=A_10 | E_135=A_10 | E_135=A_10 | ~r2_hidden(E_135, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_328])).
% 13.71/4.59  tff(c_2012, plain, (![E_334, F_335, B_336, C_337]: (k4_tarski(E_334, F_335)=k4_tarski(B_336, C_337) | ~r2_hidden(F_335, k1_tarski(C_337)) | ~r2_hidden(E_334, k1_tarski(B_336)))), inference(resolution, [status(thm)], [c_1982, c_337])).
% 13.71/4.59  tff(c_2059, plain, (![E_338, A_339, B_340]: (k4_tarski(E_338, A_339)=k4_tarski(B_340, A_339) | ~r2_hidden(E_338, k1_tarski(B_340)))), inference(resolution, [status(thm)], [c_163, c_2012])).
% 13.71/4.59  tff(c_2273, plain, (![B_348, B_349, A_350]: (k4_tarski('#skF_9'(k1_wellord2(k1_tarski(B_348)), B_349), A_350)=k4_tarski(B_348, A_350) | r1_tarski(k1_wellord2(k1_tarski(B_348)), B_349))), inference(resolution, [status(thm)], [c_831, c_2059])).
% 13.71/4.59  tff(c_74, plain, (![A_56, B_66]: (~r2_hidden(k4_tarski('#skF_9'(A_56, B_66), '#skF_10'(A_56, B_66)), B_66) | r1_tarski(A_56, B_66) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.71/4.59  tff(c_2368, plain, (![B_348, B_349]: (~r2_hidden(k4_tarski(B_348, '#skF_10'(k1_wellord2(k1_tarski(B_348)), B_349)), B_349) | r1_tarski(k1_wellord2(k1_tarski(B_348)), B_349) | ~v1_relat_1(k1_wellord2(k1_tarski(B_348))) | r1_tarski(k1_wellord2(k1_tarski(B_348)), B_349))), inference(superposition, [status(thm), theory('equality')], [c_2273, c_74])).
% 13.71/4.59  tff(c_2415, plain, (![B_348, B_349]: (~r2_hidden(k4_tarski(B_348, '#skF_10'(k1_wellord2(k1_tarski(B_348)), B_349)), B_349) | r1_tarski(k1_wellord2(k1_tarski(B_348)), B_349))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2368])).
% 13.71/4.59  tff(c_7425, plain, (![A_636]: (r1_tarski(k1_wellord2(k1_tarski(A_636)), k1_tarski(k4_tarski(A_636, A_636))))), inference(resolution, [status(thm)], [c_7346, c_2415])).
% 13.71/4.59  tff(c_251, plain, (![A_124, C_125]: (r1_tarski(k1_tarski(A_124), C_125) | ~r2_hidden(A_124, C_125) | ~r2_hidden(A_124, C_125))), inference(superposition, [status(thm), theory('equality')], [c_32, c_236])).
% 13.71/4.59  tff(c_257, plain, (![A_124, C_125]: (k1_tarski(A_124)=C_125 | ~r1_tarski(C_125, k1_tarski(A_124)) | ~r2_hidden(A_124, C_125))), inference(resolution, [status(thm)], [c_251, c_2])).
% 13.71/4.59  tff(c_7453, plain, (![A_637]: (k1_wellord2(k1_tarski(A_637))=k1_tarski(k4_tarski(A_637, A_637)) | ~r2_hidden(k4_tarski(A_637, A_637), k1_wellord2(k1_tarski(A_637))))), inference(resolution, [status(thm)], [c_7425, c_257])).
% 13.71/4.59  tff(c_7469, plain, (![D_83]: (k1_wellord2(k1_tarski(D_83))=k1_tarski(k4_tarski(D_83, D_83)) | ~r1_tarski(D_83, D_83) | ~r2_hidden(D_83, k1_tarski(D_83)))), inference(resolution, [status(thm)], [c_106, c_7453])).
% 13.71/4.59  tff(c_7472, plain, (![D_83]: (k1_wellord2(k1_tarski(D_83))=k1_tarski(k4_tarski(D_83, D_83)))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_6, c_7469])).
% 13.71/4.59  tff(c_102, plain, (k1_wellord2(k1_tarski('#skF_13'))!=k1_tarski(k4_tarski('#skF_13', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.71/4.59  tff(c_7504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7472, c_102])).
% 13.71/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.71/4.59  
% 13.71/4.59  Inference rules
% 13.71/4.59  ----------------------
% 13.71/4.59  #Ref     : 0
% 13.71/4.59  #Sup     : 1909
% 13.71/4.59  #Fact    : 2
% 13.71/4.59  #Define  : 0
% 13.71/4.59  #Split   : 0
% 13.71/4.59  #Chain   : 0
% 13.71/4.59  #Close   : 0
% 13.71/4.59  
% 13.71/4.59  Ordering : KBO
% 13.71/4.59  
% 13.71/4.59  Simplification rules
% 13.71/4.59  ----------------------
% 13.71/4.59  #Subsume      : 215
% 13.71/4.59  #Demod        : 538
% 13.71/4.59  #Tautology    : 183
% 13.71/4.59  #SimpNegUnit  : 0
% 13.71/4.59  #BackRed      : 1
% 13.71/4.59  
% 13.71/4.59  #Partial instantiations: 0
% 13.71/4.59  #Strategies tried      : 1
% 13.71/4.59  
% 13.71/4.59  Timing (in seconds)
% 13.71/4.59  ----------------------
% 13.71/4.60  Preprocessing        : 0.60
% 13.71/4.60  Parsing              : 0.28
% 13.71/4.60  CNF conversion       : 0.05
% 13.71/4.60  Main loop            : 3.11
% 13.71/4.60  Inferencing          : 0.90
% 13.71/4.60  Reduction            : 1.06
% 13.71/4.60  Demodulation         : 0.83
% 13.71/4.60  BG Simplification    : 0.16
% 13.71/4.60  Subsumption          : 0.78
% 13.71/4.60  Abstraction          : 0.16
% 13.71/4.60  MUC search           : 0.00
% 13.71/4.60  Cooper               : 0.00
% 13.71/4.60  Total                : 3.78
% 13.71/4.60  Index Insertion      : 0.00
% 13.71/4.60  Index Deletion       : 0.00
% 13.71/4.60  Index Matching       : 0.00
% 13.71/4.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
