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
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 260 expanded)
%              Number of leaves         :   29 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 485 expanded)
%              Number of equality atoms :   42 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_184,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1432,plain,(
    ! [A_164,B_165,B_166] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_164,B_165),B_166),B_165)
      | r1_xboole_0(k4_xboole_0(A_164,B_165),B_166) ) ),
    inference(resolution,[status(thm)],[c_184,c_6])).

tff(c_1470,plain,(
    ! [A_167,B_168] : r1_xboole_0(k4_xboole_0(A_167,B_168),B_168) ),
    inference(resolution,[status(thm)],[c_30,c_1432])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1491,plain,(
    ! [B_169,A_170] : r1_xboole_0(B_169,k4_xboole_0(A_170,B_169)) ),
    inference(resolution,[status(thm)],[c_1470,c_26])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1584,plain,(
    ! [B_173,A_174] : k3_xboole_0(B_173,k4_xboole_0(A_174,B_173)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1491,c_22])).

tff(c_40,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_178,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,k4_xboole_0(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_605,plain,(
    ! [A_24,B_25] : k3_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_1665,plain,(
    ! [A_175] : k4_xboole_0(A_175,A_175) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1584,c_605])).

tff(c_109,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_113,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109,c_38])).

tff(c_1731,plain,(
    ! [A_175] : k3_xboole_0(A_175,A_175) = A_175 ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_113])).

tff(c_1720,plain,(
    ! [A_175] : k4_xboole_0(A_175,k1_xboole_0) = k3_xboole_0(A_175,A_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_42])).

tff(c_2537,plain,(
    ! [A_175] : k4_xboole_0(A_175,k1_xboole_0) = A_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_1720])).

tff(c_133,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_142,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(k1_tarski(A_51),B_52) = k1_xboole_0
      | r2_hidden(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_133,c_22])).

tff(c_606,plain,(
    ! [A_109,B_110] : k3_xboole_0(A_109,k4_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_15691,plain,(
    ! [A_422,B_423] :
      ( k4_xboole_0(k1_tarski(A_422),B_423) = k1_xboole_0
      | r2_hidden(A_422,k4_xboole_0(k1_tarski(A_422),B_423)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_606])).

tff(c_1509,plain,(
    ! [B_169,A_170] : k3_xboole_0(B_169,k4_xboole_0(A_170,B_169)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1491,c_22])).

tff(c_218,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_367,plain,(
    ! [D_82,A_83,B_84] :
      ( r2_hidden(D_82,A_83)
      | ~ r2_hidden(D_82,k3_xboole_0(A_83,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_218])).

tff(c_1295,plain,(
    ! [D_160,A_161,B_162] :
      ( r2_hidden(D_160,k1_tarski(A_161))
      | ~ r2_hidden(D_160,k1_xboole_0)
      | r2_hidden(A_161,B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_367])).

tff(c_54,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_144,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_54])).

tff(c_50,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_311,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,B_78)
      | ~ r2_hidden(C_79,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_782,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ r2_hidden(C_121,B_122)
      | ~ r2_hidden(C_121,k1_tarski(A_123))
      | r2_hidden(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_50,c_311])).

tff(c_800,plain,(
    ! [A_123] :
      ( ~ r2_hidden('#skF_4',k1_tarski(A_123))
      | r2_hidden(A_123,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_782])).

tff(c_1381,plain,(
    ! [A_161,B_162] :
      ( r2_hidden(A_161,'#skF_5')
      | ~ r2_hidden('#skF_4',k1_xboole_0)
      | r2_hidden(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_1295,c_800])).

tff(c_1431,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1381])).

tff(c_1512,plain,(
    ! [A_171,B_172] : k3_xboole_0(k4_xboole_0(A_171,B_172),B_172) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1470,c_22])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k3_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_752,plain,(
    ! [C_117,B_118,A_119] :
      ( ~ r2_hidden(C_117,B_118)
      | ~ r2_hidden(C_117,A_119)
      | k3_xboole_0(A_119,B_118) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_311])).

tff(c_771,plain,(
    ! [A_120] :
      ( ~ r2_hidden('#skF_4',A_120)
      | k3_xboole_0(A_120,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_752])).

tff(c_775,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(k4_xboole_0(A_3,B_4),'#skF_5') != k1_xboole_0
      | r2_hidden('#skF_4',B_4)
      | ~ r2_hidden('#skF_4',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_771])).

tff(c_883,plain,(
    ! [A_132,B_133] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(A_132,B_133)) != k1_xboole_0
      | r2_hidden('#skF_4',B_133)
      | ~ r2_hidden('#skF_4',A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_775])).

tff(c_893,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(A_22,B_23)) != k1_xboole_0
      | r2_hidden('#skF_4',k3_xboole_0(A_22,B_23))
      | ~ r2_hidden('#skF_4',A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_883])).

tff(c_1520,plain,(
    ! [A_171,B_172] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(k4_xboole_0(A_171,B_172),B_172)) != k1_xboole_0
      | r2_hidden('#skF_4',k1_xboole_0)
      | ~ r2_hidden('#skF_4',k4_xboole_0(A_171,B_172)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_893])).

tff(c_4599,plain,(
    ! [A_256,B_257] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(k4_xboole_0(A_256,B_257),B_257)) != k1_xboole_0
      | ~ r2_hidden('#skF_4',k4_xboole_0(A_256,B_257)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1431,c_1520])).

tff(c_4653,plain,(
    ! [A_256] : ~ r2_hidden('#skF_4',k4_xboole_0(A_256,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_4599])).

tff(c_15766,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15691,c_4653])).

tff(c_16017,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15766,c_42])).

tff(c_16109,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2,c_16017])).

tff(c_16111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_16109])).

tff(c_16113,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1381])).

tff(c_555,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(D_97,A_98)
      | ~ r2_hidden(D_97,k3_xboole_0(B_99,A_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_567,plain,(
    ! [D_97,B_52,A_51] :
      ( r2_hidden(D_97,B_52)
      | ~ r2_hidden(D_97,k1_xboole_0)
      | r2_hidden(A_51,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_555])).

tff(c_16134,plain,(
    ! [B_52,A_51] :
      ( r2_hidden('#skF_4',B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_16113,c_567])).

tff(c_16314,plain,(
    ! [B_52] : r2_hidden('#skF_4',B_52) ),
    inference(factorization,[status(thm),theory(equality)],[c_16134])).

tff(c_16484,plain,(
    ! [B_432] : r2_hidden('#skF_4',B_432) ),
    inference(factorization,[status(thm),theory(equality)],[c_16134])).

tff(c_175,plain,(
    ! [D_8,A_60,B_61] :
      ( ~ r2_hidden(D_8,k4_xboole_0(A_60,B_61))
      | ~ r2_hidden(D_8,k3_xboole_0(A_60,B_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_6])).

tff(c_16494,plain,(
    ! [A_60,B_61] : ~ r2_hidden('#skF_4',k3_xboole_0(A_60,B_61)) ),
    inference(resolution,[status(thm)],[c_16484,c_175])).

tff(c_16526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16314,c_16494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.17  
% 9.27/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 9.27/3.17  
% 9.27/3.17  %Foreground sorts:
% 9.27/3.17  
% 9.27/3.17  
% 9.27/3.17  %Background operators:
% 9.27/3.17  
% 9.27/3.17  
% 9.27/3.17  %Foreground operators:
% 9.27/3.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.27/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.27/3.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.27/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.27/3.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.27/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.27/3.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.27/3.17  tff('#skF_5', type, '#skF_5': $i).
% 9.27/3.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.27/3.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.27/3.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.27/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.17  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.27/3.17  
% 9.42/3.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.42/3.19  tff(f_91, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 9.42/3.19  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.42/3.19  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.42/3.19  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.42/3.19  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.42/3.19  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.42/3.19  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.42/3.19  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.42/3.19  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.42/3.19  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.42/3.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.42/3.19  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.42/3.19  tff(c_55, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 9.42/3.19  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.42/3.19  tff(c_184, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), A_62) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.42/3.19  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.42/3.19  tff(c_1432, plain, (![A_164, B_165, B_166]: (~r2_hidden('#skF_3'(k4_xboole_0(A_164, B_165), B_166), B_165) | r1_xboole_0(k4_xboole_0(A_164, B_165), B_166))), inference(resolution, [status(thm)], [c_184, c_6])).
% 9.42/3.19  tff(c_1470, plain, (![A_167, B_168]: (r1_xboole_0(k4_xboole_0(A_167, B_168), B_168))), inference(resolution, [status(thm)], [c_30, c_1432])).
% 9.42/3.19  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.42/3.19  tff(c_1491, plain, (![B_169, A_170]: (r1_xboole_0(B_169, k4_xboole_0(A_170, B_169)))), inference(resolution, [status(thm)], [c_1470, c_26])).
% 9.42/3.19  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.42/3.19  tff(c_1584, plain, (![B_173, A_174]: (k3_xboole_0(B_173, k4_xboole_0(A_174, B_173))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1491, c_22])).
% 9.42/3.19  tff(c_40, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.42/3.19  tff(c_42, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.42/3.19  tff(c_166, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.42/3.19  tff(c_178, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k3_xboole_0(A_24, k4_xboole_0(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_166])).
% 9.42/3.19  tff(c_605, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 9.42/3.19  tff(c_1665, plain, (![A_175]: (k4_xboole_0(A_175, A_175)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1584, c_605])).
% 9.42/3.19  tff(c_109, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.42/3.19  tff(c_38, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.42/3.19  tff(c_113, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_38])).
% 9.42/3.19  tff(c_1731, plain, (![A_175]: (k3_xboole_0(A_175, A_175)=A_175)), inference(superposition, [status(thm), theory('equality')], [c_1665, c_113])).
% 9.42/3.19  tff(c_1720, plain, (![A_175]: (k4_xboole_0(A_175, k1_xboole_0)=k3_xboole_0(A_175, A_175))), inference(superposition, [status(thm), theory('equality')], [c_1665, c_42])).
% 9.42/3.19  tff(c_2537, plain, (![A_175]: (k4_xboole_0(A_175, k1_xboole_0)=A_175)), inference(demodulation, [status(thm), theory('equality')], [c_1731, c_1720])).
% 9.42/3.19  tff(c_133, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.42/3.19  tff(c_142, plain, (![A_51, B_52]: (k3_xboole_0(k1_tarski(A_51), B_52)=k1_xboole_0 | r2_hidden(A_51, B_52))), inference(resolution, [status(thm)], [c_133, c_22])).
% 9.42/3.19  tff(c_606, plain, (![A_109, B_110]: (k3_xboole_0(A_109, k4_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 9.42/3.19  tff(c_15691, plain, (![A_422, B_423]: (k4_xboole_0(k1_tarski(A_422), B_423)=k1_xboole_0 | r2_hidden(A_422, k4_xboole_0(k1_tarski(A_422), B_423)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_606])).
% 9.42/3.19  tff(c_1509, plain, (![B_169, A_170]: (k3_xboole_0(B_169, k4_xboole_0(A_170, B_169))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1491, c_22])).
% 9.42/3.19  tff(c_218, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k4_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.42/3.19  tff(c_367, plain, (![D_82, A_83, B_84]: (r2_hidden(D_82, A_83) | ~r2_hidden(D_82, k3_xboole_0(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_218])).
% 9.42/3.19  tff(c_1295, plain, (![D_160, A_161, B_162]: (r2_hidden(D_160, k1_tarski(A_161)) | ~r2_hidden(D_160, k1_xboole_0) | r2_hidden(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_142, c_367])).
% 9.42/3.19  tff(c_54, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.42/3.19  tff(c_144, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_133, c_54])).
% 9.42/3.19  tff(c_50, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.42/3.19  tff(c_311, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, B_78) | ~r2_hidden(C_79, A_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.42/3.19  tff(c_782, plain, (![C_121, B_122, A_123]: (~r2_hidden(C_121, B_122) | ~r2_hidden(C_121, k1_tarski(A_123)) | r2_hidden(A_123, B_122))), inference(resolution, [status(thm)], [c_50, c_311])).
% 9.42/3.19  tff(c_800, plain, (![A_123]: (~r2_hidden('#skF_4', k1_tarski(A_123)) | r2_hidden(A_123, '#skF_5'))), inference(resolution, [status(thm)], [c_144, c_782])).
% 9.42/3.19  tff(c_1381, plain, (![A_161, B_162]: (r2_hidden(A_161, '#skF_5') | ~r2_hidden('#skF_4', k1_xboole_0) | r2_hidden(A_161, B_162))), inference(resolution, [status(thm)], [c_1295, c_800])).
% 9.42/3.19  tff(c_1431, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1381])).
% 9.42/3.19  tff(c_1512, plain, (![A_171, B_172]: (k3_xboole_0(k4_xboole_0(A_171, B_172), B_172)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1470, c_22])).
% 9.42/3.19  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.42/3.19  tff(c_24, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k3_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.42/3.19  tff(c_752, plain, (![C_117, B_118, A_119]: (~r2_hidden(C_117, B_118) | ~r2_hidden(C_117, A_119) | k3_xboole_0(A_119, B_118)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_311])).
% 9.42/3.19  tff(c_771, plain, (![A_120]: (~r2_hidden('#skF_4', A_120) | k3_xboole_0(A_120, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_752])).
% 9.42/3.19  tff(c_775, plain, (![A_3, B_4]: (k3_xboole_0(k4_xboole_0(A_3, B_4), '#skF_5')!=k1_xboole_0 | r2_hidden('#skF_4', B_4) | ~r2_hidden('#skF_4', A_3))), inference(resolution, [status(thm)], [c_4, c_771])).
% 9.42/3.19  tff(c_883, plain, (![A_132, B_133]: (k3_xboole_0('#skF_5', k4_xboole_0(A_132, B_133))!=k1_xboole_0 | r2_hidden('#skF_4', B_133) | ~r2_hidden('#skF_4', A_132))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_775])).
% 9.42/3.19  tff(c_893, plain, (![A_22, B_23]: (k3_xboole_0('#skF_5', k4_xboole_0(A_22, B_23))!=k1_xboole_0 | r2_hidden('#skF_4', k3_xboole_0(A_22, B_23)) | ~r2_hidden('#skF_4', A_22))), inference(superposition, [status(thm), theory('equality')], [c_40, c_883])).
% 9.42/3.19  tff(c_1520, plain, (![A_171, B_172]: (k3_xboole_0('#skF_5', k4_xboole_0(k4_xboole_0(A_171, B_172), B_172))!=k1_xboole_0 | r2_hidden('#skF_4', k1_xboole_0) | ~r2_hidden('#skF_4', k4_xboole_0(A_171, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_1512, c_893])).
% 9.42/3.19  tff(c_4599, plain, (![A_256, B_257]: (k3_xboole_0('#skF_5', k4_xboole_0(k4_xboole_0(A_256, B_257), B_257))!=k1_xboole_0 | ~r2_hidden('#skF_4', k4_xboole_0(A_256, B_257)))), inference(negUnitSimplification, [status(thm)], [c_1431, c_1520])).
% 9.42/3.19  tff(c_4653, plain, (![A_256]: (~r2_hidden('#skF_4', k4_xboole_0(A_256, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1509, c_4599])).
% 9.42/3.19  tff(c_15766, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_15691, c_4653])).
% 9.42/3.19  tff(c_16017, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15766, c_42])).
% 9.42/3.19  tff(c_16109, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2, c_16017])).
% 9.42/3.19  tff(c_16111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_16109])).
% 9.42/3.19  tff(c_16113, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1381])).
% 9.42/3.19  tff(c_555, plain, (![D_97, A_98, B_99]: (r2_hidden(D_97, A_98) | ~r2_hidden(D_97, k3_xboole_0(B_99, A_98)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_367])).
% 9.42/3.19  tff(c_567, plain, (![D_97, B_52, A_51]: (r2_hidden(D_97, B_52) | ~r2_hidden(D_97, k1_xboole_0) | r2_hidden(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_142, c_555])).
% 9.42/3.19  tff(c_16134, plain, (![B_52, A_51]: (r2_hidden('#skF_4', B_52) | r2_hidden(A_51, B_52))), inference(resolution, [status(thm)], [c_16113, c_567])).
% 9.42/3.19  tff(c_16314, plain, (![B_52]: (r2_hidden('#skF_4', B_52))), inference(factorization, [status(thm), theory('equality')], [c_16134])).
% 9.42/3.19  tff(c_16484, plain, (![B_432]: (r2_hidden('#skF_4', B_432))), inference(factorization, [status(thm), theory('equality')], [c_16134])).
% 9.42/3.19  tff(c_175, plain, (![D_8, A_60, B_61]: (~r2_hidden(D_8, k4_xboole_0(A_60, B_61)) | ~r2_hidden(D_8, k3_xboole_0(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_6])).
% 9.42/3.19  tff(c_16494, plain, (![A_60, B_61]: (~r2_hidden('#skF_4', k3_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_16484, c_175])).
% 9.42/3.19  tff(c_16526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16314, c_16494])).
% 9.42/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.19  
% 9.42/3.19  Inference rules
% 9.42/3.19  ----------------------
% 9.42/3.19  #Ref     : 0
% 9.42/3.19  #Sup     : 4082
% 9.42/3.19  #Fact    : 6
% 9.42/3.19  #Define  : 0
% 9.42/3.19  #Split   : 4
% 9.42/3.19  #Chain   : 0
% 9.42/3.19  #Close   : 0
% 9.42/3.19  
% 9.42/3.19  Ordering : KBO
% 9.42/3.19  
% 9.42/3.19  Simplification rules
% 9.42/3.19  ----------------------
% 9.42/3.19  #Subsume      : 915
% 9.42/3.19  #Demod        : 3872
% 9.42/3.19  #Tautology    : 1973
% 9.42/3.19  #SimpNegUnit  : 59
% 9.42/3.19  #BackRed      : 12
% 9.42/3.19  
% 9.42/3.19  #Partial instantiations: 0
% 9.42/3.19  #Strategies tried      : 1
% 9.42/3.19  
% 9.42/3.19  Timing (in seconds)
% 9.42/3.19  ----------------------
% 9.42/3.19  Preprocessing        : 0.32
% 9.42/3.19  Parsing              : 0.17
% 9.42/3.19  CNF conversion       : 0.02
% 9.42/3.19  Main loop            : 2.11
% 9.42/3.19  Inferencing          : 0.53
% 9.42/3.19  Reduction            : 0.91
% 9.42/3.19  Demodulation         : 0.74
% 9.42/3.19  BG Simplification    : 0.07
% 9.42/3.19  Subsumption          : 0.48
% 9.42/3.19  Abstraction          : 0.09
% 9.42/3.19  MUC search           : 0.00
% 9.42/3.19  Cooper               : 0.00
% 9.42/3.19  Total                : 2.47
% 9.42/3.19  Index Insertion      : 0.00
% 9.42/3.19  Index Deletion       : 0.00
% 9.42/3.19  Index Matching       : 0.00
% 9.42/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
