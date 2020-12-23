%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 198 expanded)
%              Number of leaves         :   37 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 364 expanded)
%              Number of equality atoms :   76 ( 313 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_83,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_58,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_125,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_114,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_136,plain,(
    ! [A_70,B_71] : r1_tarski(A_70,k2_xboole_0(A_70,B_71)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_136])).

tff(c_362,plain,(
    ! [B_97,A_98] :
      ( k1_tarski(B_97) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k1_tarski(B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_365,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_139,c_362])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_114,c_365])).

tff(c_381,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_382,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_384,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_3') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_18])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_387,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_382,c_20])).

tff(c_600,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,B_123)
      | ~ r2_hidden(C_124,A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_613,plain,(
    ! [C_128] : ~ r2_hidden(C_128,'#skF_3') ),
    inference(resolution,[status(thm)],[c_387,c_600])).

tff(c_625,plain,(
    ! [A_129] : r1_xboole_0(A_129,'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_613])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( ~ r1_xboole_0(B_18,A_17)
      | ~ r1_tarski(B_18,A_17)
      | v1_xboole_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_721,plain,(
    ! [A_134] :
      ( ~ r1_tarski(A_134,'#skF_3')
      | v1_xboole_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_625,c_24])).

tff(c_733,plain,(
    ! [B_135] : v1_xboole_0(k3_xboole_0('#skF_3',B_135)) ),
    inference(resolution,[status(thm)],[c_16,c_721])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_383,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ v1_xboole_0(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_8])).

tff(c_741,plain,(
    ! [B_135] : k3_xboole_0('#skF_3',B_135) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_733,c_383])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_904,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k2_xboole_0(A_141,B_142)) = k3_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_965,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_904])).

tff(c_978,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_384,c_2,c_965])).

tff(c_440,plain,(
    ! [B_106,A_107] : k5_xboole_0(B_106,A_107) = k5_xboole_0(A_107,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_456,plain,(
    ! [A_107] : k5_xboole_0('#skF_3',A_107) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_384])).

tff(c_30,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_385,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_30])).

tff(c_654,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k5_xboole_0(A_131,B_132),C_133) = k5_xboole_0(A_131,k5_xboole_0(B_132,C_133)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_700,plain,(
    ! [A_24,C_133] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_133)) = k5_xboole_0('#skF_3',C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_654])).

tff(c_718,plain,(
    ! [A_24,C_133] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_133)) = C_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_700])).

tff(c_990,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_718])).

tff(c_997,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_990])).

tff(c_999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_997])).

tff(c_1000,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1001,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1041,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1001,c_60])).

tff(c_1042,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,A_148) = k5_xboole_0(A_148,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1058,plain,(
    ! [A_148] : k5_xboole_0(k1_xboole_0,A_148) = A_148 ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_18])).

tff(c_1446,plain,(
    ! [A_180,B_181,C_182] : k5_xboole_0(k5_xboole_0(A_180,B_181),C_182) = k5_xboole_0(A_180,k5_xboole_0(B_181,C_182)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1526,plain,(
    ! [A_24,C_182] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_182)) = k5_xboole_0(k1_xboole_0,C_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1446])).

tff(c_1542,plain,(
    ! [A_183,C_184] : k5_xboole_0(A_183,k5_xboole_0(A_183,C_184)) = C_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1526])).

tff(c_1594,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1542])).

tff(c_1017,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_62])).

tff(c_1361,plain,(
    ! [A_177,B_178] : k5_xboole_0(k5_xboole_0(A_177,B_178),k2_xboole_0(A_177,B_178)) = k3_xboole_0(A_177,B_178) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1397,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_1361])).

tff(c_1410,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_1397])).

tff(c_1687,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1594,c_1410])).

tff(c_1231,plain,(
    ! [B_169,A_170] :
      ( k1_tarski(B_169) = A_170
      | k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,k1_tarski(B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1234,plain,(
    ! [A_170] :
      ( k1_tarski('#skF_2') = A_170
      | k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_1231])).

tff(c_1288,plain,(
    ! [A_174] :
      ( A_174 = '#skF_3'
      | k1_xboole_0 = A_174
      | ~ r1_tarski(A_174,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1234])).

tff(c_1308,plain,(
    ! [B_14] :
      ( k3_xboole_0('#skF_3',B_14) = '#skF_3'
      | k3_xboole_0('#skF_3',B_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1288])).

tff(c_1778,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_1308])).

tff(c_1787,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_1778])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1041,c_1787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.23/1.51  
% 3.23/1.51  %Foreground sorts:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Background operators:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Foreground operators:
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.23/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.51  
% 3.23/1.52  tff(f_126, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.23/1.52  tff(f_79, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.23/1.52  tff(f_105, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.23/1.52  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.23/1.52  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.23/1.52  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/1.52  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.23/1.52  tff(f_77, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.23/1.52  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.52  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.23/1.52  tff(f_85, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.23/1.52  tff(f_83, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.23/1.52  tff(f_81, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.23/1.52  tff(c_58, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.23/1.52  tff(c_125, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_58])).
% 3.23/1.52  tff(c_56, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.23/1.52  tff(c_114, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_56])).
% 3.23/1.52  tff(c_62, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.23/1.52  tff(c_136, plain, (![A_70, B_71]: (r1_tarski(A_70, k2_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.52  tff(c_139, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_136])).
% 3.23/1.52  tff(c_362, plain, (![B_97, A_98]: (k1_tarski(B_97)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k1_tarski(B_97)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.52  tff(c_365, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_139, c_362])).
% 3.23/1.52  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_114, c_365])).
% 3.23/1.52  tff(c_381, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.23/1.52  tff(c_382, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 3.23/1.52  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.52  tff(c_384, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_3')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_382, c_18])).
% 3.23/1.52  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.52  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_1'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.52  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.52  tff(c_387, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_382, c_20])).
% 3.23/1.52  tff(c_600, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, B_123) | ~r2_hidden(C_124, A_122))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.52  tff(c_613, plain, (![C_128]: (~r2_hidden(C_128, '#skF_3'))), inference(resolution, [status(thm)], [c_387, c_600])).
% 3.23/1.52  tff(c_625, plain, (![A_129]: (r1_xboole_0(A_129, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_613])).
% 3.23/1.52  tff(c_24, plain, (![B_18, A_17]: (~r1_xboole_0(B_18, A_17) | ~r1_tarski(B_18, A_17) | v1_xboole_0(B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.23/1.52  tff(c_721, plain, (![A_134]: (~r1_tarski(A_134, '#skF_3') | v1_xboole_0(A_134))), inference(resolution, [status(thm)], [c_625, c_24])).
% 3.23/1.52  tff(c_733, plain, (![B_135]: (v1_xboole_0(k3_xboole_0('#skF_3', B_135)))), inference(resolution, [status(thm)], [c_16, c_721])).
% 3.23/1.52  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.52  tff(c_383, plain, (![A_7]: (A_7='#skF_3' | ~v1_xboole_0(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_8])).
% 3.23/1.52  tff(c_741, plain, (![B_135]: (k3_xboole_0('#skF_3', B_135)='#skF_3')), inference(resolution, [status(thm)], [c_733, c_383])).
% 3.23/1.52  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.52  tff(c_904, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k2_xboole_0(A_141, B_142))=k3_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.52  tff(c_965, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_904])).
% 3.23/1.52  tff(c_978, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_741, c_384, c_2, c_965])).
% 3.23/1.52  tff(c_440, plain, (![B_106, A_107]: (k5_xboole_0(B_106, A_107)=k5_xboole_0(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.52  tff(c_456, plain, (![A_107]: (k5_xboole_0('#skF_3', A_107)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_440, c_384])).
% 3.23/1.52  tff(c_30, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_385, plain, (![A_24]: (k5_xboole_0(A_24, A_24)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_30])).
% 3.23/1.52  tff(c_654, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k5_xboole_0(A_131, B_132), C_133)=k5_xboole_0(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.52  tff(c_700, plain, (![A_24, C_133]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_133))=k5_xboole_0('#skF_3', C_133))), inference(superposition, [status(thm), theory('equality')], [c_385, c_654])).
% 3.23/1.52  tff(c_718, plain, (![A_24, C_133]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_133))=C_133)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_700])).
% 3.23/1.52  tff(c_990, plain, (k5_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_978, c_718])).
% 3.23/1.52  tff(c_997, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_384, c_990])).
% 3.23/1.52  tff(c_999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_997])).
% 3.23/1.52  tff(c_1000, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 3.23/1.52  tff(c_1001, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_56])).
% 3.23/1.52  tff(c_60, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.23/1.52  tff(c_1041, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1001, c_60])).
% 3.23/1.52  tff(c_1042, plain, (![B_147, A_148]: (k5_xboole_0(B_147, A_148)=k5_xboole_0(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.52  tff(c_1058, plain, (![A_148]: (k5_xboole_0(k1_xboole_0, A_148)=A_148)), inference(superposition, [status(thm), theory('equality')], [c_1042, c_18])).
% 3.23/1.52  tff(c_1446, plain, (![A_180, B_181, C_182]: (k5_xboole_0(k5_xboole_0(A_180, B_181), C_182)=k5_xboole_0(A_180, k5_xboole_0(B_181, C_182)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.52  tff(c_1526, plain, (![A_24, C_182]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_182))=k5_xboole_0(k1_xboole_0, C_182))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1446])).
% 3.23/1.52  tff(c_1542, plain, (![A_183, C_184]: (k5_xboole_0(A_183, k5_xboole_0(A_183, C_184))=C_184)), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1526])).
% 3.23/1.52  tff(c_1594, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1542])).
% 3.23/1.52  tff(c_1017, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_62])).
% 3.23/1.52  tff(c_1361, plain, (![A_177, B_178]: (k5_xboole_0(k5_xboole_0(A_177, B_178), k2_xboole_0(A_177, B_178))=k3_xboole_0(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.52  tff(c_1397, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_1361])).
% 3.23/1.52  tff(c_1410, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_1397])).
% 3.23/1.52  tff(c_1687, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1594, c_1410])).
% 3.23/1.52  tff(c_1231, plain, (![B_169, A_170]: (k1_tarski(B_169)=A_170 | k1_xboole_0=A_170 | ~r1_tarski(A_170, k1_tarski(B_169)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.52  tff(c_1234, plain, (![A_170]: (k1_tarski('#skF_2')=A_170 | k1_xboole_0=A_170 | ~r1_tarski(A_170, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_1231])).
% 3.23/1.52  tff(c_1288, plain, (![A_174]: (A_174='#skF_3' | k1_xboole_0=A_174 | ~r1_tarski(A_174, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1234])).
% 3.23/1.52  tff(c_1308, plain, (![B_14]: (k3_xboole_0('#skF_3', B_14)='#skF_3' | k3_xboole_0('#skF_3', B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1288])).
% 3.23/1.52  tff(c_1778, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1687, c_1308])).
% 3.23/1.52  tff(c_1787, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1687, c_1778])).
% 3.23/1.52  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1041, c_1787])).
% 3.23/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  Inference rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Ref     : 0
% 3.23/1.52  #Sup     : 401
% 3.23/1.52  #Fact    : 1
% 3.23/1.52  #Define  : 0
% 3.23/1.52  #Split   : 3
% 3.23/1.52  #Chain   : 0
% 3.23/1.52  #Close   : 0
% 3.23/1.52  
% 3.23/1.52  Ordering : KBO
% 3.23/1.52  
% 3.23/1.52  Simplification rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Subsume      : 11
% 3.23/1.52  #Demod        : 167
% 3.23/1.52  #Tautology    : 263
% 3.23/1.52  #SimpNegUnit  : 8
% 3.23/1.52  #BackRed      : 10
% 3.23/1.52  
% 3.23/1.52  #Partial instantiations: 0
% 3.23/1.52  #Strategies tried      : 1
% 3.23/1.52  
% 3.23/1.52  Timing (in seconds)
% 3.23/1.52  ----------------------
% 3.23/1.53  Preprocessing        : 0.32
% 3.23/1.53  Parsing              : 0.17
% 3.23/1.53  CNF conversion       : 0.02
% 3.23/1.53  Main loop            : 0.44
% 3.23/1.53  Inferencing          : 0.16
% 3.23/1.53  Reduction            : 0.17
% 3.23/1.53  Demodulation         : 0.13
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.06
% 3.23/1.53  Abstraction          : 0.02
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.80
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
