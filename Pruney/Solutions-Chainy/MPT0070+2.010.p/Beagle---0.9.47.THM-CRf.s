%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.75s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_263,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_271,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_34])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_298,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_316,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_320,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_316])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_272,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_272])).

tff(c_565,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(k2_xboole_0(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_589,plain,(
    ! [C_59] :
      ( r1_tarski('#skF_1',C_59)
      | ~ r1_tarski('#skF_2',C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_565])).

tff(c_594,plain,(
    ! [B_18] :
      ( r1_tarski('#skF_1',B_18)
      | k4_xboole_0('#skF_2',B_18) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_589])).

tff(c_30,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_235,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_243,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_4])).

tff(c_436,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_457,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_436])).

tff(c_478,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_457])).

tff(c_875,plain,(
    ! [C_72,B_73,A_74] :
      ( r1_tarski(k4_xboole_0(C_72,B_73),k4_xboole_0(C_72,A_74))
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5499,plain,(
    ! [C_166,B_167,A_168] :
      ( k4_xboole_0(k4_xboole_0(C_166,B_167),k4_xboole_0(C_166,A_168)) = k1_xboole_0
      | ~ r1_tarski(A_168,B_167) ) ),
    inference(resolution,[status(thm)],[c_875,c_22])).

tff(c_5647,plain,(
    ! [A_168] :
      ( k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',A_168)) = k1_xboole_0
      | ~ r1_tarski(A_168,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_5499])).

tff(c_12227,plain,(
    ! [A_258] :
      ( k3_xboole_0('#skF_3',A_258) = k1_xboole_0
      | ~ r1_tarski(A_258,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5647])).

tff(c_12263,plain,
    ( k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0
    | k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_594,c_12227])).

tff(c_12282,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_4,c_12263])).

tff(c_12284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_12282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:27:19 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.46  
% 6.75/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.46  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.75/2.46  
% 6.75/2.46  %Foreground sorts:
% 6.75/2.46  
% 6.75/2.46  
% 6.75/2.46  %Background operators:
% 6.75/2.46  
% 6.75/2.46  
% 6.75/2.46  %Foreground operators:
% 6.75/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.75/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.75/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.75/2.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.75/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.75/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.75/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.75/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.75/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.75/2.46  
% 6.75/2.47  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.75/2.47  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.75/2.47  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.75/2.47  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.75/2.47  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.75/2.47  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.75/2.47  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 6.75/2.47  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.75/2.47  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.75/2.47  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.75/2.47  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 6.75/2.47  tff(c_263, plain, (![A_41, B_42]: (r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.75/2.47  tff(c_34, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.75/2.47  tff(c_271, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_34])).
% 6.75/2.47  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.75/2.47  tff(c_26, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.75/2.47  tff(c_298, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.75/2.47  tff(c_316, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_298])).
% 6.75/2.47  tff(c_320, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_316])).
% 6.75/2.47  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.75/2.47  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.75/2.47  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.75/2.47  tff(c_272, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.75/2.47  tff(c_280, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_272])).
% 6.75/2.47  tff(c_565, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(k2_xboole_0(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.75/2.47  tff(c_589, plain, (![C_59]: (r1_tarski('#skF_1', C_59) | ~r1_tarski('#skF_2', C_59))), inference(superposition, [status(thm), theory('equality')], [c_280, c_565])).
% 6.75/2.47  tff(c_594, plain, (![B_18]: (r1_tarski('#skF_1', B_18) | k4_xboole_0('#skF_2', B_18)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_589])).
% 6.75/2.47  tff(c_30, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.75/2.47  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.75/2.47  tff(c_235, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.75/2.47  tff(c_239, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_235])).
% 6.75/2.47  tff(c_243, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_239, c_4])).
% 6.75/2.47  tff(c_436, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.75/2.47  tff(c_457, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_243, c_436])).
% 6.75/2.47  tff(c_478, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_457])).
% 6.75/2.47  tff(c_875, plain, (![C_72, B_73, A_74]: (r1_tarski(k4_xboole_0(C_72, B_73), k4_xboole_0(C_72, A_74)) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.75/2.47  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.75/2.47  tff(c_5499, plain, (![C_166, B_167, A_168]: (k4_xboole_0(k4_xboole_0(C_166, B_167), k4_xboole_0(C_166, A_168))=k1_xboole_0 | ~r1_tarski(A_168, B_167))), inference(resolution, [status(thm)], [c_875, c_22])).
% 6.75/2.47  tff(c_5647, plain, (![A_168]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', A_168))=k1_xboole_0 | ~r1_tarski(A_168, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_478, c_5499])).
% 6.75/2.47  tff(c_12227, plain, (![A_258]: (k3_xboole_0('#skF_3', A_258)=k1_xboole_0 | ~r1_tarski(A_258, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5647])).
% 6.75/2.47  tff(c_12263, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0 | k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_594, c_12227])).
% 6.75/2.47  tff(c_12282, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_320, c_4, c_12263])).
% 6.75/2.47  tff(c_12284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_12282])).
% 6.75/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.47  
% 6.75/2.47  Inference rules
% 6.75/2.47  ----------------------
% 6.75/2.47  #Ref     : 1
% 6.75/2.47  #Sup     : 3093
% 6.75/2.47  #Fact    : 0
% 6.75/2.47  #Define  : 0
% 6.75/2.47  #Split   : 7
% 6.75/2.47  #Chain   : 0
% 6.75/2.47  #Close   : 0
% 6.75/2.47  
% 6.75/2.47  Ordering : KBO
% 6.75/2.47  
% 6.75/2.47  Simplification rules
% 6.75/2.47  ----------------------
% 6.75/2.47  #Subsume      : 821
% 6.75/2.47  #Demod        : 1911
% 6.75/2.47  #Tautology    : 1605
% 6.75/2.47  #SimpNegUnit  : 103
% 6.75/2.47  #BackRed      : 2
% 6.75/2.47  
% 6.75/2.47  #Partial instantiations: 0
% 6.75/2.47  #Strategies tried      : 1
% 6.75/2.47  
% 6.75/2.47  Timing (in seconds)
% 6.75/2.47  ----------------------
% 6.75/2.48  Preprocessing        : 0.28
% 6.75/2.48  Parsing              : 0.16
% 6.75/2.48  CNF conversion       : 0.02
% 6.75/2.48  Main loop            : 1.43
% 6.75/2.48  Inferencing          : 0.39
% 6.75/2.48  Reduction            : 0.65
% 6.75/2.48  Demodulation         : 0.52
% 6.75/2.48  BG Simplification    : 0.04
% 6.75/2.48  Subsumption          : 0.26
% 6.75/2.48  Abstraction          : 0.05
% 6.75/2.48  MUC search           : 0.00
% 6.75/2.48  Cooper               : 0.00
% 6.75/2.48  Total                : 1.73
% 6.75/2.48  Index Insertion      : 0.00
% 6.75/2.48  Index Deletion       : 0.00
% 6.75/2.48  Index Matching       : 0.00
% 6.75/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
