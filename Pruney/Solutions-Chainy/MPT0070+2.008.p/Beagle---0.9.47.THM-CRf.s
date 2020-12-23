%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  78 expanded)
%              Number of equality atoms :   34 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_276,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_284,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_276,c_34])).

tff(c_20,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_431,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_472,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_431])).

tff(c_485,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_472])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_235,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_243,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_235])).

tff(c_407,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(k2_xboole_0(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_560,plain,(
    ! [C_59] :
      ( r1_tarski('#skF_1',C_59)
      | ~ r1_tarski('#skF_2',C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_407])).

tff(c_565,plain,(
    ! [B_8] :
      ( r1_tarski('#skF_1',B_8)
      | k4_xboole_0('#skF_2',B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_560])).

tff(c_30,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_248,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_248])).

tff(c_256,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_4])).

tff(c_325,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_337,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_325])).

tff(c_356,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_337])).

tff(c_841,plain,(
    ! [C_74,B_75,A_76] :
      ( r1_tarski(k4_xboole_0(C_74,B_75),k4_xboole_0(C_74,A_76))
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6230,plain,(
    ! [C_175,B_176,A_177] :
      ( k4_xboole_0(k4_xboole_0(C_175,B_176),k4_xboole_0(C_175,A_177)) = k1_xboole_0
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(resolution,[status(thm)],[c_841,c_12])).

tff(c_6394,plain,(
    ! [A_177] :
      ( k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',A_177)) = k1_xboole_0
      | ~ r1_tarski(A_177,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_6230])).

tff(c_9726,plain,(
    ! [A_226] :
      ( k3_xboole_0('#skF_3',A_226) = k1_xboole_0
      | ~ r1_tarski(A_226,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6394])).

tff(c_9758,plain,
    ( k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0
    | k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_565,c_9726])).

tff(c_9776,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_4,c_9758])).

tff(c_9778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_9776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.30  
% 6.27/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.30  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.27/2.30  
% 6.27/2.30  %Foreground sorts:
% 6.27/2.30  
% 6.27/2.30  
% 6.27/2.30  %Background operators:
% 6.27/2.30  
% 6.27/2.30  
% 6.27/2.30  %Foreground operators:
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.27/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.27/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.27/2.30  
% 6.27/2.31  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.27/2.31  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.27/2.31  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.27/2.31  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.27/2.31  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.27/2.31  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.27/2.31  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.27/2.31  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.27/2.31  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.27/2.31  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.27/2.31  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 6.27/2.31  tff(c_276, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.27/2.31  tff(c_34, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.31  tff(c_284, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_276, c_34])).
% 6.27/2.31  tff(c_20, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.27/2.31  tff(c_26, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.27/2.31  tff(c_431, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.27/2.31  tff(c_472, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_431])).
% 6.27/2.31  tff(c_485, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_472])).
% 6.27/2.31  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.27/2.31  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.27/2.31  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.31  tff(c_235, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.27/2.31  tff(c_243, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_235])).
% 6.27/2.31  tff(c_407, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(k2_xboole_0(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.27/2.31  tff(c_560, plain, (![C_59]: (r1_tarski('#skF_1', C_59) | ~r1_tarski('#skF_2', C_59))), inference(superposition, [status(thm), theory('equality')], [c_243, c_407])).
% 6.27/2.31  tff(c_565, plain, (![B_8]: (r1_tarski('#skF_1', B_8) | k4_xboole_0('#skF_2', B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_560])).
% 6.27/2.31  tff(c_30, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.27/2.31  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.31  tff(c_248, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.27/2.31  tff(c_252, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_248])).
% 6.27/2.31  tff(c_256, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_252, c_4])).
% 6.27/2.31  tff(c_325, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.27/2.31  tff(c_337, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_256, c_325])).
% 6.27/2.31  tff(c_356, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_337])).
% 6.27/2.31  tff(c_841, plain, (![C_74, B_75, A_76]: (r1_tarski(k4_xboole_0(C_74, B_75), k4_xboole_0(C_74, A_76)) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.27/2.31  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.27/2.31  tff(c_6230, plain, (![C_175, B_176, A_177]: (k4_xboole_0(k4_xboole_0(C_175, B_176), k4_xboole_0(C_175, A_177))=k1_xboole_0 | ~r1_tarski(A_177, B_176))), inference(resolution, [status(thm)], [c_841, c_12])).
% 6.27/2.31  tff(c_6394, plain, (![A_177]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', A_177))=k1_xboole_0 | ~r1_tarski(A_177, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_356, c_6230])).
% 6.27/2.31  tff(c_9726, plain, (![A_226]: (k3_xboole_0('#skF_3', A_226)=k1_xboole_0 | ~r1_tarski(A_226, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6394])).
% 6.27/2.31  tff(c_9758, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0 | k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_565, c_9726])).
% 6.27/2.31  tff(c_9776, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_485, c_4, c_9758])).
% 6.27/2.31  tff(c_9778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_9776])).
% 6.27/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.31  
% 6.27/2.31  Inference rules
% 6.27/2.31  ----------------------
% 6.27/2.31  #Ref     : 1
% 6.27/2.31  #Sup     : 2441
% 6.27/2.31  #Fact    : 0
% 6.27/2.31  #Define  : 0
% 6.27/2.31  #Split   : 6
% 6.27/2.31  #Chain   : 0
% 6.27/2.31  #Close   : 0
% 6.27/2.31  
% 6.27/2.31  Ordering : KBO
% 6.27/2.31  
% 6.27/2.31  Simplification rules
% 6.27/2.31  ----------------------
% 6.27/2.31  #Subsume      : 571
% 6.27/2.31  #Demod        : 1523
% 6.27/2.31  #Tautology    : 1339
% 6.27/2.31  #SimpNegUnit  : 50
% 6.27/2.31  #BackRed      : 0
% 6.27/2.31  
% 6.27/2.31  #Partial instantiations: 0
% 6.27/2.31  #Strategies tried      : 1
% 6.27/2.31  
% 6.27/2.31  Timing (in seconds)
% 6.27/2.31  ----------------------
% 6.54/2.32  Preprocessing        : 0.29
% 6.54/2.32  Parsing              : 0.17
% 6.54/2.32  CNF conversion       : 0.02
% 6.54/2.32  Main loop            : 1.27
% 6.54/2.32  Inferencing          : 0.34
% 6.54/2.32  Reduction            : 0.58
% 6.54/2.32  Demodulation         : 0.47
% 6.54/2.32  BG Simplification    : 0.04
% 6.54/2.32  Subsumption          : 0.23
% 6.54/2.32  Abstraction          : 0.05
% 6.54/2.32  MUC search           : 0.00
% 6.54/2.32  Cooper               : 0.00
% 6.54/2.32  Total                : 1.59
% 6.54/2.32  Index Insertion      : 0.00
% 6.54/2.32  Index Deletion       : 0.00
% 6.54/2.32  Index Matching       : 0.00
% 6.54/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
