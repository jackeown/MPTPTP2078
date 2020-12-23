%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  40 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_71,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [E_10,A_4,C_6] : r2_hidden(E_10,k1_enumset1(A_4,E_10,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_8])).

tff(c_44,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k3_tarski(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_565,plain,(
    ! [A_136,A_137,B_138] :
      ( r1_tarski(A_136,k2_xboole_0(A_137,B_138))
      | ~ r2_hidden(A_136,k2_tarski(A_137,B_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_67])).

tff(c_574,plain,(
    ! [A_139,B_140] : r1_tarski(A_139,k2_xboole_0(A_139,B_140)) ),
    inference(resolution,[status(thm)],[c_80,c_565])).

tff(c_54,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_236,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(A_81,C_82)
      | ~ r1_tarski(B_83,C_82)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,'#skF_5')
      | ~ r1_tarski(A_81,k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_54,c_236])).

tff(c_589,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_574,c_242])).

tff(c_50,plain,(
    ! [A_45,C_47,B_46] :
      ( r2_hidden(A_45,C_47)
      | ~ r1_tarski(k2_tarski(A_45,B_46),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_626,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_589,c_50])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:30:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.47  
% 2.69/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.48  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.69/1.48  
% 2.69/1.48  %Foreground sorts:
% 2.69/1.48  
% 2.69/1.48  
% 2.69/1.48  %Background operators:
% 2.69/1.48  
% 2.69/1.48  
% 2.69/1.48  %Foreground operators:
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.69/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.69/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.69/1.48  
% 2.69/1.49  tff(f_77, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.69/1.49  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.69/1.49  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.69/1.49  tff(f_66, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.69/1.49  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.69/1.49  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.69/1.49  tff(f_72, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.69/1.49  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.69/1.49  tff(c_71, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.49  tff(c_8, plain, (![E_10, A_4, C_6]: (r2_hidden(E_10, k1_enumset1(A_4, E_10, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.49  tff(c_80, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_8])).
% 2.69/1.49  tff(c_44, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.49  tff(c_67, plain, (![A_59, B_60]: (r1_tarski(A_59, k3_tarski(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.49  tff(c_565, plain, (![A_136, A_137, B_138]: (r1_tarski(A_136, k2_xboole_0(A_137, B_138)) | ~r2_hidden(A_136, k2_tarski(A_137, B_138)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_67])).
% 2.69/1.49  tff(c_574, plain, (![A_139, B_140]: (r1_tarski(A_139, k2_xboole_0(A_139, B_140)))), inference(resolution, [status(thm)], [c_80, c_565])).
% 2.69/1.49  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.69/1.49  tff(c_236, plain, (![A_81, C_82, B_83]: (r1_tarski(A_81, C_82) | ~r1_tarski(B_83, C_82) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.49  tff(c_242, plain, (![A_81]: (r1_tarski(A_81, '#skF_5') | ~r1_tarski(A_81, k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_54, c_236])).
% 2.69/1.49  tff(c_589, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_574, c_242])).
% 2.69/1.49  tff(c_50, plain, (![A_45, C_47, B_46]: (r2_hidden(A_45, C_47) | ~r1_tarski(k2_tarski(A_45, B_46), C_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.69/1.49  tff(c_626, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_589, c_50])).
% 2.69/1.49  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_626])).
% 2.69/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.49  
% 2.69/1.49  Inference rules
% 2.69/1.49  ----------------------
% 2.69/1.49  #Ref     : 0
% 2.69/1.49  #Sup     : 119
% 2.69/1.49  #Fact    : 0
% 2.69/1.49  #Define  : 0
% 2.69/1.49  #Split   : 0
% 2.69/1.49  #Chain   : 0
% 2.69/1.49  #Close   : 0
% 2.69/1.49  
% 2.69/1.49  Ordering : KBO
% 2.69/1.49  
% 2.69/1.49  Simplification rules
% 2.69/1.49  ----------------------
% 2.69/1.49  #Subsume      : 0
% 2.69/1.49  #Demod        : 61
% 2.69/1.49  #Tautology    : 68
% 2.69/1.49  #SimpNegUnit  : 1
% 2.69/1.49  #BackRed      : 0
% 2.69/1.49  
% 2.69/1.49  #Partial instantiations: 0
% 2.69/1.49  #Strategies tried      : 1
% 2.69/1.49  
% 2.69/1.49  Timing (in seconds)
% 2.69/1.49  ----------------------
% 2.69/1.49  Preprocessing        : 0.42
% 2.69/1.49  Parsing              : 0.22
% 2.69/1.49  CNF conversion       : 0.03
% 2.69/1.49  Main loop            : 0.28
% 2.69/1.49  Inferencing          : 0.10
% 2.69/1.49  Reduction            : 0.10
% 2.69/1.49  Demodulation         : 0.08
% 2.69/1.49  BG Simplification    : 0.02
% 2.69/1.49  Subsumption          : 0.05
% 2.69/1.49  Abstraction          : 0.02
% 2.69/1.49  MUC search           : 0.00
% 2.69/1.49  Cooper               : 0.00
% 2.69/1.49  Total                : 0.73
% 2.69/1.49  Index Insertion      : 0.00
% 2.69/1.49  Index Deletion       : 0.00
% 2.69/1.49  Index Matching       : 0.00
% 2.69/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
