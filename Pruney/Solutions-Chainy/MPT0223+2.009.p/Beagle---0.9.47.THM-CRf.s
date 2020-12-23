%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:18 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_38,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),k1_tarski(B_30))
      | B_30 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,k3_xboole_0(A_49,B_48)) = B_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_175,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_162])).

tff(c_411,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,C_83)
      | ~ r1_xboole_0(A_82,k2_xboole_0(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1211,plain,(
    ! [A_145] :
      ( r1_xboole_0(A_145,k1_tarski('#skF_1'))
      | ~ r1_xboole_0(A_145,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_411])).

tff(c_1336,plain,(
    ! [A_152] :
      ( r1_xboole_0(k1_tarski(A_152),k1_tarski('#skF_1'))
      | A_152 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_36,c_1211])).

tff(c_34,plain,(
    ! [B_28] : ~ r1_xboole_0(k1_tarski(B_28),k1_tarski(B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1345,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1336,c_34])).

tff(c_1351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.44  
% 3.08/1.45  tff(f_86, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.08/1.45  tff(f_81, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.08/1.45  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.08/1.45  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.08/1.45  tff(f_63, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.08/1.45  tff(f_76, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 3.08/1.45  tff(c_38, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.08/1.45  tff(c_36, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), k1_tarski(B_30)) | B_30=A_29)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.45  tff(c_40, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.08/1.45  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.45  tff(c_95, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k3_xboole_0(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.45  tff(c_162, plain, (![B_48, A_49]: (k2_xboole_0(B_48, k3_xboole_0(A_49, B_48))=B_48)), inference(superposition, [status(thm), theory('equality')], [c_4, c_95])).
% 3.08/1.45  tff(c_175, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_40, c_162])).
% 3.08/1.45  tff(c_411, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, C_83) | ~r1_xboole_0(A_82, k2_xboole_0(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.08/1.45  tff(c_1211, plain, (![A_145]: (r1_xboole_0(A_145, k1_tarski('#skF_1')) | ~r1_xboole_0(A_145, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_175, c_411])).
% 3.08/1.45  tff(c_1336, plain, (![A_152]: (r1_xboole_0(k1_tarski(A_152), k1_tarski('#skF_1')) | A_152='#skF_2')), inference(resolution, [status(thm)], [c_36, c_1211])).
% 3.08/1.45  tff(c_34, plain, (![B_28]: (~r1_xboole_0(k1_tarski(B_28), k1_tarski(B_28)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.45  tff(c_1345, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1336, c_34])).
% 3.08/1.45  tff(c_1351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1345])).
% 3.08/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.45  
% 3.08/1.45  Inference rules
% 3.08/1.45  ----------------------
% 3.08/1.45  #Ref     : 0
% 3.08/1.45  #Sup     : 320
% 3.08/1.45  #Fact    : 0
% 3.08/1.45  #Define  : 0
% 3.08/1.45  #Split   : 0
% 3.08/1.45  #Chain   : 0
% 3.08/1.45  #Close   : 0
% 3.08/1.45  
% 3.08/1.45  Ordering : KBO
% 3.08/1.45  
% 3.08/1.45  Simplification rules
% 3.08/1.45  ----------------------
% 3.08/1.45  #Subsume      : 6
% 3.08/1.45  #Demod        : 122
% 3.08/1.45  #Tautology    : 172
% 3.08/1.45  #SimpNegUnit  : 1
% 3.08/1.45  #BackRed      : 0
% 3.08/1.45  
% 3.08/1.45  #Partial instantiations: 0
% 3.08/1.45  #Strategies tried      : 1
% 3.08/1.45  
% 3.08/1.45  Timing (in seconds)
% 3.08/1.45  ----------------------
% 3.08/1.45  Preprocessing        : 0.29
% 3.08/1.45  Parsing              : 0.16
% 3.08/1.45  CNF conversion       : 0.02
% 3.08/1.45  Main loop            : 0.40
% 3.08/1.45  Inferencing          : 0.14
% 3.08/1.45  Reduction            : 0.14
% 3.08/1.45  Demodulation         : 0.11
% 3.08/1.45  BG Simplification    : 0.02
% 3.08/1.46  Subsumption          : 0.07
% 3.08/1.46  Abstraction          : 0.02
% 3.08/1.46  MUC search           : 0.00
% 3.08/1.46  Cooper               : 0.00
% 3.08/1.46  Total                : 0.71
% 3.08/1.46  Index Insertion      : 0.00
% 3.08/1.46  Index Deletion       : 0.00
% 3.08/1.46  Index Matching       : 0.00
% 3.08/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
