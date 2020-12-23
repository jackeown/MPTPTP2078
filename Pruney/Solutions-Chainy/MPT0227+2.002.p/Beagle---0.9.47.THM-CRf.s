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
% DateTime   : Thu Dec  3 09:48:50 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_30,plain,(
    ! [A_20,B_21] : r1_tarski(k1_tarski(A_20),k2_tarski(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_311,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_tarski(k4_xboole_0(A_58,B_59),C_60)
      | ~ r1_tarski(A_58,k2_xboole_0(B_59,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_82,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_xboole_0(A_32,C_33)
      | ~ r1_tarski(A_32,k4_xboole_0(B_34,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_38,A_39] :
      ( r1_xboole_0(A_38,A_39)
      | ~ r1_tarski(A_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_82])).

tff(c_24,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_116,c_24])).

tff(c_327,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,k2_xboole_0(B_59,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_311,c_121])).

tff(c_425,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_451,plain,(
    ! [A_20,B_21] : k4_xboole_0(k1_tarski(A_20),k2_tarski(A_20,B_21)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_425])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.04/1.21  
% 2.04/1.21  %Foreground sorts:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Background operators:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Foreground operators:
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.21  
% 2.04/1.22  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.04/1.22  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.04/1.22  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.04/1.22  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.04/1.22  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.04/1.22  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.04/1.22  tff(f_72, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.04/1.22  tff(c_30, plain, (![A_20, B_21]: (r1_tarski(k1_tarski(A_20), k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.22  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.22  tff(c_311, plain, (![A_58, B_59, C_60]: (r1_tarski(k4_xboole_0(A_58, B_59), C_60) | ~r1_tarski(A_58, k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.22  tff(c_60, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.22  tff(c_67, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_60])).
% 2.04/1.22  tff(c_82, plain, (![A_32, C_33, B_34]: (r1_xboole_0(A_32, C_33) | ~r1_tarski(A_32, k4_xboole_0(B_34, C_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.22  tff(c_116, plain, (![A_38, A_39]: (r1_xboole_0(A_38, A_39) | ~r1_tarski(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_67, c_82])).
% 2.04/1.22  tff(c_24, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.22  tff(c_121, plain, (![A_39]: (k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_116, c_24])).
% 2.04/1.22  tff(c_327, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, k2_xboole_0(B_59, k1_xboole_0)))), inference(resolution, [status(thm)], [c_311, c_121])).
% 2.04/1.22  tff(c_425, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_tarski(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 2.04/1.22  tff(c_451, plain, (![A_20, B_21]: (k4_xboole_0(k1_tarski(A_20), k2_tarski(A_20, B_21))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_425])).
% 2.04/1.22  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.22  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_451, c_32])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 93
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 0
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 3
% 2.04/1.22  #Demod        : 57
% 2.04/1.22  #Tautology    : 59
% 2.04/1.22  #SimpNegUnit  : 0
% 2.04/1.22  #BackRed      : 1
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.22  Preprocessing        : 0.29
% 2.04/1.22  Parsing              : 0.15
% 2.04/1.22  CNF conversion       : 0.02
% 2.04/1.22  Main loop            : 0.20
% 2.04/1.22  Inferencing          : 0.07
% 2.04/1.23  Reduction            : 0.07
% 2.04/1.23  Demodulation         : 0.05
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.04
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.51
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
