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
% DateTime   : Thu Dec  3 09:43:21 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 115 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_263,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_276,plain,(
    ! [A_16,C_43] :
      ( ~ r1_xboole_0(A_16,k1_xboole_0)
      | ~ r2_hidden(C_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_263])).

tff(c_278,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_406,plain,(
    ! [A_53,B_54] :
      ( ~ r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_263])).

tff(c_410,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_147,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_160,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_175,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_160])).

tff(c_181,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_175])).

tff(c_356,plain,(
    ! [A_50,B_51,C_52] : k3_xboole_0(k3_xboole_0(A_50,B_51),C_52) = k3_xboole_0(A_50,k3_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_817,plain,(
    ! [C_65] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_65)) = k3_xboole_0('#skF_3',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_356])).

tff(c_855,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_817])).

tff(c_871,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_855])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_883,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_4])).

tff(c_897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_278,c_883])).

tff(c_898,plain,(
    ! [A_16] : ~ r1_xboole_0(A_16,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_902,plain,(
    ! [A_69,B_70] :
      ( ~ r1_xboole_0(A_69,B_70)
      | k3_xboole_0(A_69,B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_263])).

tff(c_906,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_902])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_910,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_6])).

tff(c_917,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_910])).

tff(c_1211,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),k3_xboole_0(A_82,B_83))
      | r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1235,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1211])).

tff(c_1241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_898,c_917,c_1235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.47  
% 2.62/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.62/1.47  
% 2.62/1.47  %Foreground sorts:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Background operators:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Foreground operators:
% 2.62/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.47  
% 2.94/1.48  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.94/1.48  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.94/1.48  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.94/1.48  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.94/1.48  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.94/1.48  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.94/1.48  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.94/1.48  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.94/1.48  tff(c_28, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.94/1.48  tff(c_18, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.48  tff(c_263, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.48  tff(c_276, plain, (![A_16, C_43]: (~r1_xboole_0(A_16, k1_xboole_0) | ~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_263])).
% 2.94/1.48  tff(c_278, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_276])).
% 2.94/1.48  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.94/1.48  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.48  tff(c_406, plain, (![A_53, B_54]: (~r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_263])).
% 2.94/1.48  tff(c_410, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_406])).
% 2.94/1.48  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.48  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.94/1.48  tff(c_147, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.48  tff(c_155, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_147])).
% 2.94/1.48  tff(c_160, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.48  tff(c_175, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_155, c_160])).
% 2.94/1.48  tff(c_181, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_175])).
% 2.94/1.48  tff(c_356, plain, (![A_50, B_51, C_52]: (k3_xboole_0(k3_xboole_0(A_50, B_51), C_52)=k3_xboole_0(A_50, k3_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.48  tff(c_817, plain, (![C_65]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_65))=k3_xboole_0('#skF_3', C_65))), inference(superposition, [status(thm), theory('equality')], [c_181, c_356])).
% 2.94/1.48  tff(c_855, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_410, c_817])).
% 2.94/1.48  tff(c_871, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_855])).
% 2.94/1.48  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.48  tff(c_883, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_871, c_4])).
% 2.94/1.48  tff(c_897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_278, c_883])).
% 2.94/1.48  tff(c_898, plain, (![A_16]: (~r1_xboole_0(A_16, k1_xboole_0))), inference(splitRight, [status(thm)], [c_276])).
% 2.94/1.48  tff(c_902, plain, (![A_69, B_70]: (~r1_xboole_0(A_69, B_70) | k3_xboole_0(A_69, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_263])).
% 2.94/1.48  tff(c_906, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_902])).
% 2.94/1.48  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.48  tff(c_910, plain, (![C_7]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_906, c_6])).
% 2.94/1.48  tff(c_917, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_910])).
% 2.94/1.48  tff(c_1211, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), k3_xboole_0(A_82, B_83)) | r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.48  tff(c_1235, plain, (![A_16]: (r2_hidden('#skF_1'(A_16, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1211])).
% 2.94/1.48  tff(c_1241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_898, c_917, c_1235])).
% 2.94/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  Inference rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Ref     : 0
% 2.94/1.48  #Sup     : 303
% 2.94/1.48  #Fact    : 0
% 2.94/1.48  #Define  : 0
% 2.94/1.48  #Split   : 3
% 2.94/1.48  #Chain   : 0
% 2.94/1.48  #Close   : 0
% 2.94/1.48  
% 2.94/1.48  Ordering : KBO
% 2.94/1.48  
% 2.94/1.48  Simplification rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Subsume      : 3
% 2.94/1.48  #Demod        : 239
% 2.94/1.48  #Tautology    : 205
% 2.94/1.48  #SimpNegUnit  : 8
% 2.94/1.48  #BackRed      : 3
% 2.94/1.48  
% 2.94/1.48  #Partial instantiations: 0
% 2.94/1.48  #Strategies tried      : 1
% 2.94/1.48  
% 2.94/1.48  Timing (in seconds)
% 2.94/1.48  ----------------------
% 2.94/1.49  Preprocessing        : 0.30
% 2.94/1.49  Parsing              : 0.17
% 2.94/1.49  CNF conversion       : 0.02
% 2.94/1.49  Main loop            : 0.39
% 2.94/1.49  Inferencing          : 0.14
% 2.94/1.49  Reduction            : 0.15
% 2.94/1.49  Demodulation         : 0.12
% 2.94/1.49  BG Simplification    : 0.02
% 2.94/1.49  Subsumption          : 0.05
% 2.94/1.49  Abstraction          : 0.02
% 2.94/1.49  MUC search           : 0.00
% 2.94/1.49  Cooper               : 0.00
% 2.94/1.49  Total                : 0.72
% 2.94/1.49  Index Insertion      : 0.00
% 2.94/1.49  Index Deletion       : 0.00
% 2.94/1.49  Index Matching       : 0.00
% 2.94/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
