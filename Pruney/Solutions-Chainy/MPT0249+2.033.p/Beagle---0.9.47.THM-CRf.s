%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 200 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 367 expanded)
%              Number of equality atoms :   53 ( 186 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_66,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_89,plain,(
    ! [A_61,B_62] : r1_tarski(A_61,k2_xboole_0(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_215,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_228,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_215])).

tff(c_234,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_440,plain,(
    ! [D_105,B_106,A_107] :
      ( D_105 = B_106
      | D_105 = A_107
      | ~ r2_hidden(D_105,k2_tarski(A_107,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_464,plain,(
    ! [D_108,A_109] :
      ( D_108 = A_109
      | D_108 = A_109
      | ~ r2_hidden(D_108,k1_tarski(A_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_440])).

tff(c_648,plain,(
    ! [A_133,B_134] :
      ( '#skF_1'(k1_tarski(A_133),B_134) = A_133
      | r1_tarski(k1_tarski(A_133),B_134) ) ),
    inference(resolution,[status(thm)],[c_6,c_464])).

tff(c_666,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_648,c_234])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_675,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_4])).

tff(c_680,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_675])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_518,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_600,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_2'(A_126),B_127)
      | ~ r1_tarski(A_126,B_127)
      | k1_xboole_0 = A_126 ) ),
    inference(resolution,[status(thm)],[c_8,c_518])).

tff(c_454,plain,(
    ! [D_105,A_23] :
      ( D_105 = A_23
      | D_105 = A_23
      | ~ r2_hidden(D_105,k1_tarski(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_440])).

tff(c_743,plain,(
    ! [A_142,A_143] :
      ( A_142 = '#skF_2'(A_143)
      | ~ r1_tarski(A_143,k1_tarski(A_142))
      | k1_xboole_0 = A_143 ) ),
    inference(resolution,[status(thm)],[c_600,c_454])).

tff(c_757,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_743])).

tff(c_767,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_757])).

tff(c_775,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_8])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_680,c_775])).

tff(c_781,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_195,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,k2_xboole_0(C_77,B_78))
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k1_tarski('#skF_5'))
      | ~ r1_tarski(A_76,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_195])).

tff(c_815,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,'#skF_6')
      | ~ r1_tarski(A_144,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_207])).

tff(c_820,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_815])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_822,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_820,c_10])).

tff(c_828,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_822])).

tff(c_1026,plain,(
    ! [D_169,B_170,A_171] :
      ( D_169 = B_170
      | D_169 = A_171
      | ~ r2_hidden(D_169,k2_tarski(A_171,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1055,plain,(
    ! [D_172,A_173] :
      ( D_172 = A_173
      | D_172 = A_173
      | ~ r2_hidden(D_172,k1_tarski(A_173)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1026])).

tff(c_1123,plain,(
    ! [D_179] :
      ( D_179 = '#skF_5'
      | D_179 = '#skF_5'
      | ~ r2_hidden(D_179,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_1055])).

tff(c_1149,plain,(
    ! [B_180] :
      ( '#skF_1'('#skF_6',B_180) = '#skF_5'
      | r1_tarski('#skF_6',B_180) ) ),
    inference(resolution,[status(thm)],[c_6,c_1123])).

tff(c_1175,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1149,c_828])).

tff(c_1186,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_4])).

tff(c_1191,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_828,c_1186])).

tff(c_1292,plain,(
    ! [C_184,B_185,A_186] :
      ( r2_hidden(C_184,B_185)
      | ~ r2_hidden(C_184,A_186)
      | ~ r1_tarski(A_186,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1396,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_2'(A_195),B_196)
      | ~ r1_tarski(A_195,B_196)
      | k1_xboole_0 = A_195 ) ),
    inference(resolution,[status(thm)],[c_8,c_1292])).

tff(c_1066,plain,(
    ! [D_172] :
      ( D_172 = '#skF_5'
      | D_172 = '#skF_5'
      | ~ r2_hidden(D_172,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_1055])).

tff(c_1440,plain,(
    ! [A_198] :
      ( '#skF_2'(A_198) = '#skF_5'
      | ~ r1_tarski(A_198,'#skF_6')
      | k1_xboole_0 = A_198 ) ),
    inference(resolution,[status(thm)],[c_1396,c_1066])).

tff(c_1447,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_820,c_1440])).

tff(c_1457,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1447])).

tff(c_1467,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_8])).

tff(c_1472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1191,c_1467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.52  
% 3.22/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 3.22/1.52  
% 3.22/1.52  %Foreground sorts:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Background operators:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Foreground operators:
% 3.22/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.22/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.52  
% 3.38/1.54  tff(f_100, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.38/1.54  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.54  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.38/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.54  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.54  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.38/1.54  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.38/1.54  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.38/1.54  tff(c_62, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.54  tff(c_66, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.54  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.54  tff(c_64, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.54  tff(c_68, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.54  tff(c_89, plain, (![A_61, B_62]: (r1_tarski(A_61, k2_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.54  tff(c_92, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_89])).
% 3.38/1.54  tff(c_215, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.54  tff(c_228, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_92, c_215])).
% 3.38/1.54  tff(c_234, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_228])).
% 3.38/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.54  tff(c_40, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_440, plain, (![D_105, B_106, A_107]: (D_105=B_106 | D_105=A_107 | ~r2_hidden(D_105, k2_tarski(A_107, B_106)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.54  tff(c_464, plain, (![D_108, A_109]: (D_108=A_109 | D_108=A_109 | ~r2_hidden(D_108, k1_tarski(A_109)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_440])).
% 3.38/1.54  tff(c_648, plain, (![A_133, B_134]: ('#skF_1'(k1_tarski(A_133), B_134)=A_133 | r1_tarski(k1_tarski(A_133), B_134))), inference(resolution, [status(thm)], [c_6, c_464])).
% 3.38/1.54  tff(c_666, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_648, c_234])).
% 3.38/1.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.54  tff(c_675, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_666, c_4])).
% 3.38/1.54  tff(c_680, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_234, c_675])).
% 3.38/1.54  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.38/1.54  tff(c_518, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.54  tff(c_600, plain, (![A_126, B_127]: (r2_hidden('#skF_2'(A_126), B_127) | ~r1_tarski(A_126, B_127) | k1_xboole_0=A_126)), inference(resolution, [status(thm)], [c_8, c_518])).
% 3.38/1.54  tff(c_454, plain, (![D_105, A_23]: (D_105=A_23 | D_105=A_23 | ~r2_hidden(D_105, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_440])).
% 3.38/1.54  tff(c_743, plain, (![A_142, A_143]: (A_142='#skF_2'(A_143) | ~r1_tarski(A_143, k1_tarski(A_142)) | k1_xboole_0=A_143)), inference(resolution, [status(thm)], [c_600, c_454])).
% 3.38/1.54  tff(c_757, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_92, c_743])).
% 3.38/1.54  tff(c_767, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_757])).
% 3.38/1.54  tff(c_775, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_767, c_8])).
% 3.38/1.54  tff(c_780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_680, c_775])).
% 3.38/1.54  tff(c_781, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_228])).
% 3.38/1.54  tff(c_195, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, k2_xboole_0(C_77, B_78)) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.54  tff(c_207, plain, (![A_76]: (r1_tarski(A_76, k1_tarski('#skF_5')) | ~r1_tarski(A_76, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_195])).
% 3.38/1.54  tff(c_815, plain, (![A_144]: (r1_tarski(A_144, '#skF_6') | ~r1_tarski(A_144, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_781, c_207])).
% 3.38/1.54  tff(c_820, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_14, c_815])).
% 3.38/1.54  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.54  tff(c_822, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_820, c_10])).
% 3.38/1.54  tff(c_828, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_822])).
% 3.38/1.54  tff(c_1026, plain, (![D_169, B_170, A_171]: (D_169=B_170 | D_169=A_171 | ~r2_hidden(D_169, k2_tarski(A_171, B_170)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.54  tff(c_1055, plain, (![D_172, A_173]: (D_172=A_173 | D_172=A_173 | ~r2_hidden(D_172, k1_tarski(A_173)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1026])).
% 3.38/1.54  tff(c_1123, plain, (![D_179]: (D_179='#skF_5' | D_179='#skF_5' | ~r2_hidden(D_179, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_781, c_1055])).
% 3.38/1.54  tff(c_1149, plain, (![B_180]: ('#skF_1'('#skF_6', B_180)='#skF_5' | r1_tarski('#skF_6', B_180))), inference(resolution, [status(thm)], [c_6, c_1123])).
% 3.38/1.54  tff(c_1175, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_1149, c_828])).
% 3.38/1.54  tff(c_1186, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1175, c_4])).
% 3.38/1.54  tff(c_1191, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_828, c_1186])).
% 3.38/1.54  tff(c_1292, plain, (![C_184, B_185, A_186]: (r2_hidden(C_184, B_185) | ~r2_hidden(C_184, A_186) | ~r1_tarski(A_186, B_185))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.54  tff(c_1396, plain, (![A_195, B_196]: (r2_hidden('#skF_2'(A_195), B_196) | ~r1_tarski(A_195, B_196) | k1_xboole_0=A_195)), inference(resolution, [status(thm)], [c_8, c_1292])).
% 3.38/1.54  tff(c_1066, plain, (![D_172]: (D_172='#skF_5' | D_172='#skF_5' | ~r2_hidden(D_172, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_781, c_1055])).
% 3.38/1.54  tff(c_1440, plain, (![A_198]: ('#skF_2'(A_198)='#skF_5' | ~r1_tarski(A_198, '#skF_6') | k1_xboole_0=A_198)), inference(resolution, [status(thm)], [c_1396, c_1066])).
% 3.38/1.54  tff(c_1447, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_820, c_1440])).
% 3.38/1.54  tff(c_1457, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_1447])).
% 3.38/1.54  tff(c_1467, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1457, c_8])).
% 3.38/1.54  tff(c_1472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1191, c_1467])).
% 3.38/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.54  
% 3.38/1.54  Inference rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Ref     : 0
% 3.38/1.54  #Sup     : 325
% 3.38/1.54  #Fact    : 0
% 3.38/1.54  #Define  : 0
% 3.38/1.54  #Split   : 1
% 3.38/1.54  #Chain   : 0
% 3.38/1.54  #Close   : 0
% 3.38/1.54  
% 3.38/1.54  Ordering : KBO
% 3.38/1.54  
% 3.38/1.54  Simplification rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Subsume      : 36
% 3.38/1.54  #Demod        : 113
% 3.38/1.54  #Tautology    : 172
% 3.38/1.54  #SimpNegUnit  : 21
% 3.38/1.54  #BackRed      : 6
% 3.38/1.54  
% 3.38/1.54  #Partial instantiations: 0
% 3.38/1.54  #Strategies tried      : 1
% 3.38/1.54  
% 3.38/1.54  Timing (in seconds)
% 3.38/1.54  ----------------------
% 3.38/1.54  Preprocessing        : 0.34
% 3.38/1.54  Parsing              : 0.18
% 3.38/1.54  CNF conversion       : 0.02
% 3.38/1.54  Main loop            : 0.43
% 3.38/1.54  Inferencing          : 0.15
% 3.38/1.54  Reduction            : 0.14
% 3.38/1.54  Demodulation         : 0.10
% 3.38/1.54  BG Simplification    : 0.02
% 3.38/1.54  Subsumption          : 0.08
% 3.38/1.54  Abstraction          : 0.02
% 3.38/1.54  MUC search           : 0.00
% 3.38/1.54  Cooper               : 0.00
% 3.38/1.54  Total                : 0.80
% 3.38/1.54  Index Insertion      : 0.00
% 3.38/1.54  Index Deletion       : 0.00
% 3.38/1.54  Index Matching       : 0.00
% 3.38/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
