%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 105 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_963,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(A_83,B_84)
      | k4_xboole_0(A_83,B_84) != A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_184,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_192,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_184,c_60])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_203,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_226,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_271,plain,(
    ! [A_49,B_50] : r1_xboole_0(k3_xboole_0(A_49,B_50),k5_xboole_0(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    r1_xboole_0('#skF_1',k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_271])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_305,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_283,c_24])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_468,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_18])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_481,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_468,c_16])).

tff(c_28,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_317,plain,(
    ! [A_51] : r1_xboole_0(k3_xboole_0(A_51,A_51),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_271])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_327,plain,(
    ! [A_51] : k3_xboole_0(k3_xboole_0(A_51,A_51),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_511,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_327])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_540,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_611,plain,(
    ! [C_62] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_62)) = k4_xboole_0('#skF_1',C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_540])).

tff(c_630,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_611])).

tff(c_768,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_630])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_768])).

tff(c_770,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_971,plain,(
    k4_xboole_0('#skF_1','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_963,c_770])).

tff(c_771,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1079,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1105,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_771,c_1079])).

tff(c_1226,plain,(
    ! [A_97,B_98,C_99] : k4_xboole_0(k3_xboole_0(A_97,B_98),C_99) = k3_xboole_0(A_97,k4_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2272,plain,(
    ! [C_125] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_125)) = k4_xboole_0('#skF_1',C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_1226])).

tff(c_1106,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_1079])).

tff(c_2284,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2272,c_1106])).

tff(c_2311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_971,c_2284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.57  
% 3.04/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.57  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.57  
% 3.04/1.57  %Foreground sorts:
% 3.04/1.57  
% 3.04/1.57  
% 3.04/1.57  %Background operators:
% 3.04/1.57  
% 3.04/1.57  
% 3.04/1.57  %Foreground operators:
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.57  
% 3.04/1.59  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.04/1.59  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.04/1.59  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.04/1.59  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.59  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.04/1.59  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.04/1.59  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.04/1.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.04/1.59  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.04/1.59  tff(c_963, plain, (![A_83, B_84]: (r1_xboole_0(A_83, B_84) | k4_xboole_0(A_83, B_84)!=A_83)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.59  tff(c_184, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.59  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.59  tff(c_60, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 3.04/1.59  tff(c_192, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_184, c_60])).
% 3.04/1.59  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.59  tff(c_203, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.59  tff(c_226, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_203])).
% 3.04/1.59  tff(c_271, plain, (![A_49, B_50]: (r1_xboole_0(k3_xboole_0(A_49, B_50), k5_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.59  tff(c_283, plain, (r1_xboole_0('#skF_1', k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_226, c_271])).
% 3.04/1.59  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.59  tff(c_305, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))='#skF_1'), inference(resolution, [status(thm)], [c_283, c_24])).
% 3.04/1.59  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.59  tff(c_468, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_305, c_18])).
% 3.04/1.59  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.59  tff(c_481, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_468, c_16])).
% 3.04/1.59  tff(c_28, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.59  tff(c_317, plain, (![A_51]: (r1_xboole_0(k3_xboole_0(A_51, A_51), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_271])).
% 3.04/1.59  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.04/1.59  tff(c_327, plain, (![A_51]: (k3_xboole_0(k3_xboole_0(A_51, A_51), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_317, c_2])).
% 3.04/1.59  tff(c_511, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_481, c_327])).
% 3.04/1.59  tff(c_61, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.59  tff(c_69, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_61])).
% 3.04/1.59  tff(c_540, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.59  tff(c_611, plain, (![C_62]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_62))=k4_xboole_0('#skF_1', C_62))), inference(superposition, [status(thm), theory('equality')], [c_226, c_540])).
% 3.04/1.59  tff(c_630, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_611])).
% 3.04/1.59  tff(c_768, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_511, c_630])).
% 3.04/1.59  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_768])).
% 3.04/1.59  tff(c_770, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.04/1.59  tff(c_971, plain, (k4_xboole_0('#skF_1', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_963, c_770])).
% 3.04/1.59  tff(c_771, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.04/1.59  tff(c_1079, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.59  tff(c_1105, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_771, c_1079])).
% 3.04/1.59  tff(c_1226, plain, (![A_97, B_98, C_99]: (k4_xboole_0(k3_xboole_0(A_97, B_98), C_99)=k3_xboole_0(A_97, k4_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.59  tff(c_2272, plain, (![C_125]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_125))=k4_xboole_0('#skF_1', C_125))), inference(superposition, [status(thm), theory('equality')], [c_1105, c_1226])).
% 3.04/1.59  tff(c_1106, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_1079])).
% 3.04/1.59  tff(c_2284, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2272, c_1106])).
% 3.04/1.59  tff(c_2311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_971, c_2284])).
% 3.04/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.59  
% 3.04/1.59  Inference rules
% 3.04/1.59  ----------------------
% 3.04/1.59  #Ref     : 0
% 3.04/1.59  #Sup     : 603
% 3.04/1.59  #Fact    : 0
% 3.04/1.59  #Define  : 0
% 3.04/1.59  #Split   : 1
% 3.04/1.59  #Chain   : 0
% 3.04/1.59  #Close   : 0
% 3.04/1.59  
% 3.04/1.59  Ordering : KBO
% 3.04/1.59  
% 3.04/1.59  Simplification rules
% 3.04/1.59  ----------------------
% 3.04/1.59  #Subsume      : 1
% 3.04/1.59  #Demod        : 365
% 3.04/1.59  #Tautology    : 408
% 3.04/1.59  #SimpNegUnit  : 2
% 3.04/1.59  #BackRed      : 4
% 3.04/1.59  
% 3.04/1.59  #Partial instantiations: 0
% 3.04/1.59  #Strategies tried      : 1
% 3.04/1.59  
% 3.04/1.59  Timing (in seconds)
% 3.04/1.59  ----------------------
% 3.04/1.59  Preprocessing        : 0.26
% 3.04/1.59  Parsing              : 0.14
% 3.04/1.59  CNF conversion       : 0.02
% 3.04/1.59  Main loop            : 0.49
% 3.04/1.59  Inferencing          : 0.17
% 3.04/1.59  Reduction            : 0.18
% 3.04/1.59  Demodulation         : 0.13
% 3.04/1.59  BG Simplification    : 0.02
% 3.04/1.59  Subsumption          : 0.07
% 3.04/1.59  Abstraction          : 0.03
% 3.04/1.59  MUC search           : 0.00
% 3.04/1.59  Cooper               : 0.00
% 3.04/1.59  Total                : 0.78
% 3.04/1.59  Index Insertion      : 0.00
% 3.04/1.59  Index Deletion       : 0.00
% 3.04/1.59  Index Matching       : 0.00
% 3.04/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
