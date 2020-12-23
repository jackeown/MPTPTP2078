%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 168 expanded)
%              Number of leaves         :   36 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 ( 230 expanded)
%              Number of equality atoms :   66 ( 176 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1126,plain,(
    ! [B_158,C_159] : r1_tarski(k1_tarski(B_158),k2_tarski(B_158,C_159)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1129,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1126])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_240,plain,(
    ! [A_81,B_82] :
      ( k2_xboole_0(k1_tarski(A_81),B_82) = B_82
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_194,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k2_tarski(A_65,B_66),C_67) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    ! [A_2,C_67] : k2_xboole_0(k1_tarski(A_2),C_67) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_251,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_196])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_340,plain,(
    ! [B_113,D_114,A_115,C_116] :
      ( r2_hidden(B_113,D_114)
      | ~ r2_hidden(k4_tarski(A_115,B_113),k2_zfmisc_1(k1_tarski(C_116),D_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_350,plain,(
    ! [B_113,A_115] :
      ( r2_hidden(B_113,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(A_115,B_113),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_351,plain,(
    ! [A_115,B_113] : ~ r2_hidden(k4_tarski(A_115,B_113),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_350])).

tff(c_189,plain,(
    ! [B_62,C_63] : r1_tarski(k1_tarski(B_62),k2_tarski(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_192,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_189])).

tff(c_68,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_133,plain,(
    ! [A_58,B_59] : k1_mcart_1(k4_tarski(A_58,B_59)) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_142,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_133])).

tff(c_111,plain,(
    ! [A_56,B_57] : k2_mcart_1(k4_tarski(A_56,B_57)) = B_57 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_120,plain,(
    k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_66,plain,
    ( k2_mcart_1('#skF_5') = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_127,plain,
    ( '#skF_7' = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_66])).

tff(c_128,plain,(
    k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_145,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_128])).

tff(c_152,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_68])).

tff(c_253,plain,(
    ! [A_85,B_86] : k2_zfmisc_1(k1_tarski(A_85),k1_tarski(B_86)) = k1_tarski(k4_tarski(A_85,B_86)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( ~ r1_tarski(A_15,k2_zfmisc_1(A_15,B_16))
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_374,plain,(
    ! [A_125,B_126] :
      ( ~ r1_tarski(k1_tarski(A_125),k1_tarski(k4_tarski(A_125,B_126)))
      | k1_tarski(A_125) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_28])).

tff(c_377,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_374])).

tff(c_379,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_377])).

tff(c_977,plain,(
    ! [A_143,D_144,C_145] :
      ( r2_hidden(k4_tarski(A_143,D_144),k2_zfmisc_1(C_145,k1_tarski(D_144)))
      | ~ r2_hidden(A_143,C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1015,plain,(
    ! [A_143,C_145] :
      ( r2_hidden(k4_tarski(A_143,'#skF_6'),k2_zfmisc_1(C_145,k1_xboole_0))
      | ~ r2_hidden(A_143,C_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_977])).

tff(c_1043,plain,(
    ! [A_143,C_145] :
      ( r2_hidden(k4_tarski(A_143,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_143,C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1015])).

tff(c_1044,plain,(
    ! [A_143,C_145] : ~ r2_hidden(A_143,C_145) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_1043])).

tff(c_44,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(A_25,C_27)
      | k3_xboole_0(k2_tarski(A_25,B_26),C_27) != k2_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1058,plain,(
    ! [A_149,B_150,C_151] : k3_xboole_0(k2_tarski(A_149,B_150),C_151) != k2_tarski(A_149,B_150) ),
    inference(negUnitSimplification,[status(thm)],[c_1044,c_44])).

tff(c_1066,plain,(
    ! [A_152,B_153] : k2_tarski(A_152,B_153) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1058])).

tff(c_1068,plain,(
    ! [A_2] : k1_tarski(A_2) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1066])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_17,B_18] : k2_zfmisc_1(k1_tarski(A_17),k1_tarski(B_18)) = k1_tarski(k4_tarski(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_406,plain,(
    ! [A_17] : k2_zfmisc_1(k1_tarski(A_17),k1_xboole_0) = k1_tarski(k4_tarski(A_17,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_30])).

tff(c_566,plain,(
    ! [A_135] : k1_tarski(k4_tarski(A_135,'#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_406])).

tff(c_609,plain,(
    ! [A_135,B_18] : k1_tarski(k4_tarski(k4_tarski(A_135,'#skF_6'),B_18)) = k2_zfmisc_1(k1_xboole_0,k1_tarski(B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_30])).

tff(c_651,plain,(
    ! [A_135,B_18] : k1_tarski(k4_tarski(k4_tarski(A_135,'#skF_6'),B_18)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_609])).

tff(c_1076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_651])).

tff(c_1077,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_1080,plain,(
    k4_tarski('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_68])).

tff(c_1165,plain,(
    ! [A_175,B_176] :
      ( k2_xboole_0(k1_tarski(A_175),B_176) = B_176
      | ~ r2_hidden(A_175,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1136,plain,(
    ! [A_163,B_164,C_165] : k2_xboole_0(k2_tarski(A_163,B_164),C_165) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1138,plain,(
    ! [A_2,C_165] : k2_xboole_0(k1_tarski(A_2),C_165) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1136])).

tff(c_1187,plain,(
    ! [A_175] : ~ r2_hidden(A_175,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_1138])).

tff(c_1275,plain,(
    ! [A_212,C_213,B_214] :
      ( r2_hidden(A_212,C_213)
      | k3_xboole_0(k2_tarski(A_212,B_214),C_213) != k2_tarski(A_212,B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1282,plain,(
    ! [A_212,B_214] :
      ( r2_hidden(A_212,k1_xboole_0)
      | k2_tarski(A_212,B_214) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1275])).

tff(c_1285,plain,(
    ! [A_215,B_216] : k2_tarski(A_215,B_216) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_1282])).

tff(c_1287,plain,(
    ! [A_2] : k1_tarski(A_2) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1285])).

tff(c_1203,plain,(
    ! [A_186,B_187] : k2_zfmisc_1(k1_tarski(A_186),k1_tarski(B_187)) = k1_tarski(k4_tarski(A_186,B_187)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( ~ r1_tarski(A_15,k2_zfmisc_1(B_16,A_15))
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1215,plain,(
    ! [B_187,A_186] :
      ( ~ r1_tarski(k1_tarski(B_187),k1_tarski(k4_tarski(A_186,B_187)))
      | k1_tarski(B_187) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_26])).

tff(c_1302,plain,(
    ! [B_222,A_223] : ~ r1_tarski(k1_tarski(B_222),k1_tarski(k4_tarski(A_223,B_222))) ),
    inference(negUnitSimplification,[status(thm)],[c_1287,c_1215])).

tff(c_1305,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_1302])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.53  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.17/1.53  
% 3.17/1.53  %Foreground sorts:
% 3.17/1.53  
% 3.17/1.53  
% 3.17/1.53  %Background operators:
% 3.17/1.53  
% 3.17/1.53  
% 3.17/1.53  %Foreground operators:
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.17/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.17/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.17/1.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.17/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.53  
% 3.35/1.55  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.35/1.55  tff(f_74, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 3.35/1.55  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.35/1.55  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.35/1.55  tff(f_77, axiom, (![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.35/1.55  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.35/1.55  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.35/1.55  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.35/1.55  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.35/1.55  tff(f_59, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 3.35/1.55  tff(f_57, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.35/1.55  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.35/1.55  tff(f_81, axiom, (![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.35/1.55  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.55  tff(c_1126, plain, (![B_158, C_159]: (r1_tarski(k1_tarski(B_158), k2_tarski(B_158, C_159)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.55  tff(c_1129, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1126])).
% 3.35/1.55  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.35/1.55  tff(c_240, plain, (![A_81, B_82]: (k2_xboole_0(k1_tarski(A_81), B_82)=B_82 | ~r2_hidden(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.55  tff(c_194, plain, (![A_65, B_66, C_67]: (k2_xboole_0(k2_tarski(A_65, B_66), C_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.35/1.55  tff(c_196, plain, (![A_2, C_67]: (k2_xboole_0(k1_tarski(A_2), C_67)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_194])).
% 3.35/1.55  tff(c_251, plain, (![A_81]: (~r2_hidden(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_240, c_196])).
% 3.35/1.55  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.55  tff(c_340, plain, (![B_113, D_114, A_115, C_116]: (r2_hidden(B_113, D_114) | ~r2_hidden(k4_tarski(A_115, B_113), k2_zfmisc_1(k1_tarski(C_116), D_114)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.55  tff(c_350, plain, (![B_113, A_115]: (r2_hidden(B_113, k1_xboole_0) | ~r2_hidden(k4_tarski(A_115, B_113), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_340])).
% 3.35/1.55  tff(c_351, plain, (![A_115, B_113]: (~r2_hidden(k4_tarski(A_115, B_113), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_251, c_350])).
% 3.35/1.55  tff(c_189, plain, (![B_62, C_63]: (r1_tarski(k1_tarski(B_62), k2_tarski(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.55  tff(c_192, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_189])).
% 3.35/1.55  tff(c_68, plain, (k4_tarski('#skF_6', '#skF_7')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.35/1.55  tff(c_133, plain, (![A_58, B_59]: (k1_mcart_1(k4_tarski(A_58, B_59))=A_58)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.55  tff(c_142, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_68, c_133])).
% 3.35/1.55  tff(c_111, plain, (![A_56, B_57]: (k2_mcart_1(k4_tarski(A_56, B_57))=B_57)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.55  tff(c_120, plain, (k2_mcart_1('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_68, c_111])).
% 3.35/1.55  tff(c_66, plain, (k2_mcart_1('#skF_5')='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.35/1.55  tff(c_127, plain, ('#skF_7'='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_66])).
% 3.35/1.55  tff(c_128, plain, (k1_mcart_1('#skF_5')='#skF_5'), inference(splitLeft, [status(thm)], [c_127])).
% 3.35/1.55  tff(c_145, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_128])).
% 3.35/1.55  tff(c_152, plain, (k4_tarski('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_68])).
% 3.35/1.55  tff(c_253, plain, (![A_85, B_86]: (k2_zfmisc_1(k1_tarski(A_85), k1_tarski(B_86))=k1_tarski(k4_tarski(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.55  tff(c_28, plain, (![A_15, B_16]: (~r1_tarski(A_15, k2_zfmisc_1(A_15, B_16)) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.55  tff(c_374, plain, (![A_125, B_126]: (~r1_tarski(k1_tarski(A_125), k1_tarski(k4_tarski(A_125, B_126))) | k1_tarski(A_125)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_28])).
% 3.35/1.55  tff(c_377, plain, (~r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_152, c_374])).
% 3.35/1.55  tff(c_379, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_192, c_377])).
% 3.35/1.55  tff(c_977, plain, (![A_143, D_144, C_145]: (r2_hidden(k4_tarski(A_143, D_144), k2_zfmisc_1(C_145, k1_tarski(D_144))) | ~r2_hidden(A_143, C_145))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.35/1.55  tff(c_1015, plain, (![A_143, C_145]: (r2_hidden(k4_tarski(A_143, '#skF_6'), k2_zfmisc_1(C_145, k1_xboole_0)) | ~r2_hidden(A_143, C_145))), inference(superposition, [status(thm), theory('equality')], [c_379, c_977])).
% 3.35/1.55  tff(c_1043, plain, (![A_143, C_145]: (r2_hidden(k4_tarski(A_143, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_143, C_145))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1015])).
% 3.35/1.55  tff(c_1044, plain, (![A_143, C_145]: (~r2_hidden(A_143, C_145))), inference(negUnitSimplification, [status(thm)], [c_351, c_1043])).
% 3.35/1.55  tff(c_44, plain, (![A_25, C_27, B_26]: (r2_hidden(A_25, C_27) | k3_xboole_0(k2_tarski(A_25, B_26), C_27)!=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.35/1.55  tff(c_1058, plain, (![A_149, B_150, C_151]: (k3_xboole_0(k2_tarski(A_149, B_150), C_151)!=k2_tarski(A_149, B_150))), inference(negUnitSimplification, [status(thm)], [c_1044, c_44])).
% 3.35/1.55  tff(c_1066, plain, (![A_152, B_153]: (k2_tarski(A_152, B_153)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1058])).
% 3.35/1.55  tff(c_1068, plain, (![A_2]: (k1_tarski(A_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1066])).
% 3.35/1.55  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.55  tff(c_30, plain, (![A_17, B_18]: (k2_zfmisc_1(k1_tarski(A_17), k1_tarski(B_18))=k1_tarski(k4_tarski(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.55  tff(c_406, plain, (![A_17]: (k2_zfmisc_1(k1_tarski(A_17), k1_xboole_0)=k1_tarski(k4_tarski(A_17, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_379, c_30])).
% 3.35/1.55  tff(c_566, plain, (![A_135]: (k1_tarski(k4_tarski(A_135, '#skF_6'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_406])).
% 3.35/1.55  tff(c_609, plain, (![A_135, B_18]: (k1_tarski(k4_tarski(k4_tarski(A_135, '#skF_6'), B_18))=k2_zfmisc_1(k1_xboole_0, k1_tarski(B_18)))), inference(superposition, [status(thm), theory('equality')], [c_566, c_30])).
% 3.35/1.55  tff(c_651, plain, (![A_135, B_18]: (k1_tarski(k4_tarski(k4_tarski(A_135, '#skF_6'), B_18))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_609])).
% 3.35/1.55  tff(c_1076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1068, c_651])).
% 3.35/1.55  tff(c_1077, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_127])).
% 3.35/1.55  tff(c_1080, plain, (k4_tarski('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_68])).
% 3.35/1.55  tff(c_1165, plain, (![A_175, B_176]: (k2_xboole_0(k1_tarski(A_175), B_176)=B_176 | ~r2_hidden(A_175, B_176))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.55  tff(c_1136, plain, (![A_163, B_164, C_165]: (k2_xboole_0(k2_tarski(A_163, B_164), C_165)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.35/1.55  tff(c_1138, plain, (![A_2, C_165]: (k2_xboole_0(k1_tarski(A_2), C_165)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1136])).
% 3.35/1.55  tff(c_1187, plain, (![A_175]: (~r2_hidden(A_175, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_1138])).
% 3.35/1.55  tff(c_1275, plain, (![A_212, C_213, B_214]: (r2_hidden(A_212, C_213) | k3_xboole_0(k2_tarski(A_212, B_214), C_213)!=k2_tarski(A_212, B_214))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.35/1.55  tff(c_1282, plain, (![A_212, B_214]: (r2_hidden(A_212, k1_xboole_0) | k2_tarski(A_212, B_214)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1275])).
% 3.35/1.55  tff(c_1285, plain, (![A_215, B_216]: (k2_tarski(A_215, B_216)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1187, c_1282])).
% 3.35/1.55  tff(c_1287, plain, (![A_2]: (k1_tarski(A_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1285])).
% 3.35/1.55  tff(c_1203, plain, (![A_186, B_187]: (k2_zfmisc_1(k1_tarski(A_186), k1_tarski(B_187))=k1_tarski(k4_tarski(A_186, B_187)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.55  tff(c_26, plain, (![A_15, B_16]: (~r1_tarski(A_15, k2_zfmisc_1(B_16, A_15)) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.55  tff(c_1215, plain, (![B_187, A_186]: (~r1_tarski(k1_tarski(B_187), k1_tarski(k4_tarski(A_186, B_187))) | k1_tarski(B_187)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1203, c_26])).
% 3.35/1.55  tff(c_1302, plain, (![B_222, A_223]: (~r1_tarski(k1_tarski(B_222), k1_tarski(k4_tarski(A_223, B_222))))), inference(negUnitSimplification, [status(thm)], [c_1287, c_1215])).
% 3.35/1.55  tff(c_1305, plain, (~r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1080, c_1302])).
% 3.35/1.55  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1305])).
% 3.35/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  Inference rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Ref     : 0
% 3.35/1.55  #Sup     : 325
% 3.35/1.55  #Fact    : 0
% 3.35/1.55  #Define  : 0
% 3.35/1.55  #Split   : 2
% 3.35/1.55  #Chain   : 0
% 3.35/1.55  #Close   : 0
% 3.35/1.55  
% 3.35/1.55  Ordering : KBO
% 3.35/1.55  
% 3.35/1.55  Simplification rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Subsume      : 120
% 3.35/1.55  #Demod        : 154
% 3.35/1.55  #Tautology    : 144
% 3.35/1.55  #SimpNegUnit  : 37
% 3.35/1.55  #BackRed      : 16
% 3.35/1.55  
% 3.35/1.55  #Partial instantiations: 0
% 3.35/1.55  #Strategies tried      : 1
% 3.35/1.55  
% 3.35/1.55  Timing (in seconds)
% 3.35/1.55  ----------------------
% 3.35/1.55  Preprocessing        : 0.35
% 3.35/1.55  Parsing              : 0.18
% 3.35/1.55  CNF conversion       : 0.03
% 3.35/1.55  Main loop            : 0.43
% 3.35/1.56  Inferencing          : 0.15
% 3.35/1.56  Reduction            : 0.15
% 3.35/1.56  Demodulation         : 0.10
% 3.35/1.56  BG Simplification    : 0.02
% 3.35/1.56  Subsumption          : 0.07
% 3.35/1.56  Abstraction          : 0.02
% 3.35/1.56  MUC search           : 0.00
% 3.35/1.56  Cooper               : 0.00
% 3.35/1.56  Total                : 0.81
% 3.35/1.56  Index Insertion      : 0.00
% 3.35/1.56  Index Deletion       : 0.00
% 3.35/1.56  Index Matching       : 0.00
% 3.35/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
