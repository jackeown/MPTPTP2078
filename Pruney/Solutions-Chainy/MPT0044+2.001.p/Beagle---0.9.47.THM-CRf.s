%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 122 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 211 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k1_xboole_0
      <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(c_38,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_314,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,k4_xboole_0(A_58,B_59))
      | r2_hidden(D_57,B_59)
      | ~ r2_hidden(D_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_383,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,k1_xboole_0)
      | r2_hidden(D_63,'#skF_9')
      | ~ r2_hidden(D_63,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_314])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [D_63] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_63,'#skF_9')
      | ~ r2_hidden(D_63,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_383,c_2])).

tff(c_406,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_398])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_447,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_9')
      | ~ r2_hidden('#skF_2'(A_66,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_406,c_8])).

tff(c_455,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_447])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_49,c_455])).

tff(c_462,plain,(
    k4_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0
    | k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_463,plain,(
    k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_40])).

tff(c_461,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_32,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_5'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_481,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,A_75)
      | ~ r2_hidden(D_74,k4_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1271,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_161,B_162)),A_161)
      | k4_xboole_0(A_161,B_162) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_481])).

tff(c_497,plain,(
    ! [D_77,B_78,A_79] :
      ( ~ r2_hidden(D_77,B_78)
      | ~ r2_hidden(D_77,k4_xboole_0(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_511,plain,(
    ! [A_79,B_78] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_79,B_78)),B_78)
      | k4_xboole_0(A_79,B_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_497])).

tff(c_1321,plain,(
    ! [A_163] : k4_xboole_0(A_163,A_163) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1271,c_511])).

tff(c_34,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_tarski(k4_xboole_0(A_18,C_20),k4_xboole_0(B_19,C_20))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1409,plain,(
    ! [A_164,A_165] :
      ( r1_tarski(k4_xboole_0(A_164,A_165),k1_xboole_0)
      | ~ r1_tarski(A_164,A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_34])).

tff(c_513,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_524,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_5'(A_86),B_87)
      | ~ r1_tarski(A_86,B_87)
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_32,c_513])).

tff(c_541,plain,(
    ! [B_87,A_86] :
      ( ~ v1_xboole_0(B_87)
      | ~ r1_tarski(A_86,B_87)
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_524,c_2])).

tff(c_1427,plain,(
    ! [A_164,A_165] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(A_164,A_165) = k1_xboole_0
      | ~ r1_tarski(A_164,A_165) ) ),
    inference(resolution,[status(thm)],[c_1409,c_541])).

tff(c_1485,plain,(
    ! [A_168,A_169] :
      ( k4_xboole_0(A_168,A_169) = k1_xboole_0
      | ~ r1_tarski(A_168,A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1427])).

tff(c_1506,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_461,c_1485])).

tff(c_1518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_1506])).

tff(c_1520,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1534,plain,(
    k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_36])).

tff(c_1519,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1557,plain,(
    ! [D_179,A_180,B_181] :
      ( r2_hidden(D_179,A_180)
      | ~ r2_hidden(D_179,k4_xboole_0(A_180,B_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2162,plain,(
    ! [A_253,B_254] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_253,B_254)),A_253)
      | v1_xboole_0(k4_xboole_0(A_253,B_254)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1557])).

tff(c_1541,plain,(
    ! [D_176,B_177,A_178] :
      ( ~ r2_hidden(D_176,B_177)
      | ~ r2_hidden(D_176,k4_xboole_0(A_178,B_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1556,plain,(
    ! [A_178,B_177] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_178,B_177)),B_177)
      | v1_xboole_0(k4_xboole_0(A_178,B_177)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1541])).

tff(c_2206,plain,(
    ! [A_255] : v1_xboole_0(k4_xboole_0(A_255,A_255)) ),
    inference(resolution,[status(thm)],[c_2162,c_1556])).

tff(c_1521,plain,(
    ! [A_170] :
      ( r2_hidden('#skF_5'(A_170),A_170)
      | k1_xboole_0 = A_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1525,plain,(
    ! [A_170] :
      ( ~ v1_xboole_0(A_170)
      | k1_xboole_0 = A_170 ) ),
    inference(resolution,[status(thm)],[c_1521,c_2])).

tff(c_2224,plain,(
    ! [A_256] : k4_xboole_0(A_256,A_256) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2206,c_1525])).

tff(c_2472,plain,(
    ! [A_267,A_268] :
      ( r1_tarski(k4_xboole_0(A_267,A_268),k1_xboole_0)
      | ~ r1_tarski(A_267,A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2224,c_34])).

tff(c_1580,plain,(
    ! [C_185,B_186,A_187] :
      ( r2_hidden(C_185,B_186)
      | ~ r2_hidden(C_185,A_187)
      | ~ r1_tarski(A_187,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1590,plain,(
    ! [A_188,B_189] :
      ( r2_hidden('#skF_5'(A_188),B_189)
      | ~ r1_tarski(A_188,B_189)
      | k1_xboole_0 = A_188 ) ),
    inference(resolution,[status(thm)],[c_32,c_1580])).

tff(c_1607,plain,(
    ! [B_189,A_188] :
      ( ~ v1_xboole_0(B_189)
      | ~ r1_tarski(A_188,B_189)
      | k1_xboole_0 = A_188 ) ),
    inference(resolution,[status(thm)],[c_1590,c_2])).

tff(c_2490,plain,(
    ! [A_267,A_268] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(A_267,A_268) = k1_xboole_0
      | ~ r1_tarski(A_267,A_268) ) ),
    inference(resolution,[status(thm)],[c_2472,c_1607])).

tff(c_2579,plain,(
    ! [A_273,A_274] :
      ( k4_xboole_0(A_273,A_274) = k1_xboole_0
      | ~ r1_tarski(A_273,A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2490])).

tff(c_2603,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1519,c_2579])).

tff(c_2616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1534,c_2603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.65  
% 3.62/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.65  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 3.62/1.65  
% 3.62/1.65  %Foreground sorts:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Background operators:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Foreground operators:
% 3.62/1.65  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.62/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.62/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.62/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.65  
% 3.62/1.66  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.62/1.66  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.62/1.66  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.62/1.66  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.62/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.62/1.66  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.62/1.66  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 3.62/1.66  tff(c_38, plain, (r1_tarski('#skF_6', '#skF_7') | ~r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.66  tff(c_49, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.62/1.66  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.66  tff(c_42, plain, (r1_tarski('#skF_6', '#skF_7') | k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.66  tff(c_61, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.62/1.66  tff(c_314, plain, (![D_57, A_58, B_59]: (r2_hidden(D_57, k4_xboole_0(A_58, B_59)) | r2_hidden(D_57, B_59) | ~r2_hidden(D_57, A_58))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.66  tff(c_383, plain, (![D_63]: (r2_hidden(D_63, k1_xboole_0) | r2_hidden(D_63, '#skF_9') | ~r2_hidden(D_63, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_314])).
% 3.62/1.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.66  tff(c_398, plain, (![D_63]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_63, '#skF_9') | ~r2_hidden(D_63, '#skF_8'))), inference(resolution, [status(thm)], [c_383, c_2])).
% 3.62/1.66  tff(c_406, plain, (![D_64]: (r2_hidden(D_64, '#skF_9') | ~r2_hidden(D_64, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_398])).
% 3.62/1.66  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.62/1.66  tff(c_447, plain, (![A_66]: (r1_tarski(A_66, '#skF_9') | ~r2_hidden('#skF_2'(A_66, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_406, c_8])).
% 3.62/1.66  tff(c_455, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_10, c_447])).
% 3.62/1.66  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_49, c_455])).
% 3.62/1.66  tff(c_462, plain, (k4_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.62/1.66  tff(c_40, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0 | k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.66  tff(c_463, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_462, c_40])).
% 3.62/1.66  tff(c_461, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_42])).
% 3.62/1.66  tff(c_32, plain, (![A_16]: (r2_hidden('#skF_5'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.62/1.66  tff(c_481, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, A_75) | ~r2_hidden(D_74, k4_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.66  tff(c_1271, plain, (![A_161, B_162]: (r2_hidden('#skF_5'(k4_xboole_0(A_161, B_162)), A_161) | k4_xboole_0(A_161, B_162)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_481])).
% 3.62/1.66  tff(c_497, plain, (![D_77, B_78, A_79]: (~r2_hidden(D_77, B_78) | ~r2_hidden(D_77, k4_xboole_0(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.66  tff(c_511, plain, (![A_79, B_78]: (~r2_hidden('#skF_5'(k4_xboole_0(A_79, B_78)), B_78) | k4_xboole_0(A_79, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_497])).
% 3.62/1.66  tff(c_1321, plain, (![A_163]: (k4_xboole_0(A_163, A_163)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1271, c_511])).
% 3.62/1.66  tff(c_34, plain, (![A_18, C_20, B_19]: (r1_tarski(k4_xboole_0(A_18, C_20), k4_xboole_0(B_19, C_20)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.62/1.66  tff(c_1409, plain, (![A_164, A_165]: (r1_tarski(k4_xboole_0(A_164, A_165), k1_xboole_0) | ~r1_tarski(A_164, A_165))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_34])).
% 3.62/1.66  tff(c_513, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.62/1.66  tff(c_524, plain, (![A_86, B_87]: (r2_hidden('#skF_5'(A_86), B_87) | ~r1_tarski(A_86, B_87) | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_32, c_513])).
% 3.62/1.66  tff(c_541, plain, (![B_87, A_86]: (~v1_xboole_0(B_87) | ~r1_tarski(A_86, B_87) | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_524, c_2])).
% 3.62/1.66  tff(c_1427, plain, (![A_164, A_165]: (~v1_xboole_0(k1_xboole_0) | k4_xboole_0(A_164, A_165)=k1_xboole_0 | ~r1_tarski(A_164, A_165))), inference(resolution, [status(thm)], [c_1409, c_541])).
% 3.62/1.66  tff(c_1485, plain, (![A_168, A_169]: (k4_xboole_0(A_168, A_169)=k1_xboole_0 | ~r1_tarski(A_168, A_169))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1427])).
% 3.62/1.66  tff(c_1506, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_461, c_1485])).
% 3.62/1.66  tff(c_1518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_463, c_1506])).
% 3.62/1.66  tff(c_1520, plain, (r1_tarski('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_36, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0 | ~r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.66  tff(c_1534, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_36])).
% 3.62/1.66  tff(c_1519, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.66  tff(c_1557, plain, (![D_179, A_180, B_181]: (r2_hidden(D_179, A_180) | ~r2_hidden(D_179, k4_xboole_0(A_180, B_181)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.66  tff(c_2162, plain, (![A_253, B_254]: (r2_hidden('#skF_1'(k4_xboole_0(A_253, B_254)), A_253) | v1_xboole_0(k4_xboole_0(A_253, B_254)))), inference(resolution, [status(thm)], [c_4, c_1557])).
% 3.62/1.66  tff(c_1541, plain, (![D_176, B_177, A_178]: (~r2_hidden(D_176, B_177) | ~r2_hidden(D_176, k4_xboole_0(A_178, B_177)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.66  tff(c_1556, plain, (![A_178, B_177]: (~r2_hidden('#skF_1'(k4_xboole_0(A_178, B_177)), B_177) | v1_xboole_0(k4_xboole_0(A_178, B_177)))), inference(resolution, [status(thm)], [c_4, c_1541])).
% 3.62/1.66  tff(c_2206, plain, (![A_255]: (v1_xboole_0(k4_xboole_0(A_255, A_255)))), inference(resolution, [status(thm)], [c_2162, c_1556])).
% 3.62/1.66  tff(c_1521, plain, (![A_170]: (r2_hidden('#skF_5'(A_170), A_170) | k1_xboole_0=A_170)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.62/1.66  tff(c_1525, plain, (![A_170]: (~v1_xboole_0(A_170) | k1_xboole_0=A_170)), inference(resolution, [status(thm)], [c_1521, c_2])).
% 3.62/1.66  tff(c_2224, plain, (![A_256]: (k4_xboole_0(A_256, A_256)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2206, c_1525])).
% 3.62/1.66  tff(c_2472, plain, (![A_267, A_268]: (r1_tarski(k4_xboole_0(A_267, A_268), k1_xboole_0) | ~r1_tarski(A_267, A_268))), inference(superposition, [status(thm), theory('equality')], [c_2224, c_34])).
% 3.62/1.66  tff(c_1580, plain, (![C_185, B_186, A_187]: (r2_hidden(C_185, B_186) | ~r2_hidden(C_185, A_187) | ~r1_tarski(A_187, B_186))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.62/1.66  tff(c_1590, plain, (![A_188, B_189]: (r2_hidden('#skF_5'(A_188), B_189) | ~r1_tarski(A_188, B_189) | k1_xboole_0=A_188)), inference(resolution, [status(thm)], [c_32, c_1580])).
% 3.62/1.66  tff(c_1607, plain, (![B_189, A_188]: (~v1_xboole_0(B_189) | ~r1_tarski(A_188, B_189) | k1_xboole_0=A_188)), inference(resolution, [status(thm)], [c_1590, c_2])).
% 3.62/1.66  tff(c_2490, plain, (![A_267, A_268]: (~v1_xboole_0(k1_xboole_0) | k4_xboole_0(A_267, A_268)=k1_xboole_0 | ~r1_tarski(A_267, A_268))), inference(resolution, [status(thm)], [c_2472, c_1607])).
% 3.62/1.66  tff(c_2579, plain, (![A_273, A_274]: (k4_xboole_0(A_273, A_274)=k1_xboole_0 | ~r1_tarski(A_273, A_274))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2490])).
% 3.62/1.66  tff(c_2603, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1519, c_2579])).
% 3.62/1.66  tff(c_2616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1534, c_2603])).
% 3.62/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.66  
% 3.62/1.66  Inference rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Ref     : 0
% 3.62/1.66  #Sup     : 583
% 3.62/1.66  #Fact    : 0
% 3.62/1.66  #Define  : 0
% 3.62/1.66  #Split   : 6
% 3.62/1.66  #Chain   : 0
% 3.62/1.66  #Close   : 0
% 3.62/1.66  
% 3.62/1.66  Ordering : KBO
% 3.62/1.66  
% 3.62/1.66  Simplification rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Subsume      : 90
% 3.62/1.66  #Demod        : 223
% 3.62/1.66  #Tautology    : 229
% 3.62/1.66  #SimpNegUnit  : 4
% 3.62/1.66  #BackRed      : 1
% 3.62/1.66  
% 3.62/1.66  #Partial instantiations: 0
% 3.62/1.66  #Strategies tried      : 1
% 3.62/1.66  
% 3.62/1.66  Timing (in seconds)
% 3.62/1.66  ----------------------
% 3.62/1.67  Preprocessing        : 0.27
% 3.62/1.67  Parsing              : 0.14
% 3.62/1.67  CNF conversion       : 0.02
% 3.62/1.67  Main loop            : 0.58
% 3.62/1.67  Inferencing          : 0.23
% 3.62/1.67  Reduction            : 0.15
% 3.62/1.67  Demodulation         : 0.10
% 3.62/1.67  BG Simplification    : 0.03
% 3.62/1.67  Subsumption          : 0.13
% 3.62/1.67  Abstraction          : 0.03
% 3.62/1.67  MUC search           : 0.00
% 3.62/1.67  Cooper               : 0.00
% 3.62/1.67  Total                : 0.88
% 3.62/1.67  Index Insertion      : 0.00
% 3.62/1.67  Index Deletion       : 0.00
% 3.62/1.67  Index Matching       : 0.00
% 3.62/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
