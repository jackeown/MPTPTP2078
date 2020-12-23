%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  52 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_135,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_143,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_144,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_187,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_191,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_271,plain,(
    ! [A_43,B_44] : k2_xboole_0(k3_xboole_0(A_43,B_44),k4_xboole_0(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_292,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_271])).

tff(c_39,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_55,plain,(
    ! [A_25] : k2_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_14])).

tff(c_308,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_55])).

tff(c_492,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1121,plain,(
    ! [C_62] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_62)) = k4_xboole_0('#skF_3',C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_492])).

tff(c_10015,plain,(
    ! [B_174] : k4_xboole_0('#skF_3',k2_xboole_0(B_174,'#skF_5')) = k4_xboole_0('#skF_3',B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1121])).

tff(c_28,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_10122,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10015,c_129])).

tff(c_10192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_10122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.46  
% 6.71/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.71/2.46  
% 6.71/2.46  %Foreground sorts:
% 6.71/2.46  
% 6.71/2.46  
% 6.71/2.46  %Background operators:
% 6.71/2.46  
% 6.71/2.46  
% 6.71/2.46  %Foreground operators:
% 6.71/2.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.71/2.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.71/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.71/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.71/2.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.71/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.71/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.71/2.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.71/2.46  
% 6.71/2.47  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.71/2.47  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 6.71/2.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.71/2.47  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.71/2.47  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.71/2.47  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.71/2.47  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.71/2.47  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.71/2.47  tff(c_135, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.71/2.47  tff(c_24, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.71/2.47  tff(c_143, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_135, c_24])).
% 6.71/2.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.71/2.47  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.71/2.47  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.71/2.47  tff(c_144, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.71/2.47  tff(c_187, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_144])).
% 6.71/2.47  tff(c_191, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_187])).
% 6.71/2.47  tff(c_271, plain, (![A_43, B_44]: (k2_xboole_0(k3_xboole_0(A_43, B_44), k4_xboole_0(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.71/2.47  tff(c_292, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_191, c_271])).
% 6.71/2.47  tff(c_39, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.71/2.47  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.71/2.47  tff(c_55, plain, (![A_25]: (k2_xboole_0(k1_xboole_0, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_39, c_14])).
% 6.71/2.47  tff(c_308, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_292, c_55])).
% 6.71/2.47  tff(c_492, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.71/2.47  tff(c_1121, plain, (![C_62]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_62))=k4_xboole_0('#skF_3', C_62))), inference(superposition, [status(thm), theory('equality')], [c_308, c_492])).
% 6.71/2.47  tff(c_10015, plain, (![B_174]: (k4_xboole_0('#skF_3', k2_xboole_0(B_174, '#skF_5'))=k4_xboole_0('#skF_3', B_174))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1121])).
% 6.71/2.47  tff(c_28, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.71/2.47  tff(c_125, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.71/2.47  tff(c_129, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_125])).
% 6.71/2.47  tff(c_10122, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10015, c_129])).
% 6.71/2.47  tff(c_10192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_10122])).
% 6.71/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.47  
% 6.71/2.47  Inference rules
% 6.71/2.47  ----------------------
% 6.71/2.47  #Ref     : 0
% 6.71/2.47  #Sup     : 2552
% 6.71/2.47  #Fact    : 0
% 6.71/2.47  #Define  : 0
% 6.71/2.47  #Split   : 4
% 6.71/2.47  #Chain   : 0
% 6.71/2.47  #Close   : 0
% 6.71/2.47  
% 6.71/2.47  Ordering : KBO
% 6.71/2.47  
% 6.71/2.47  Simplification rules
% 6.71/2.47  ----------------------
% 6.71/2.47  #Subsume      : 17
% 6.71/2.47  #Demod        : 2947
% 6.71/2.47  #Tautology    : 1632
% 6.71/2.47  #SimpNegUnit  : 19
% 6.71/2.47  #BackRed      : 8
% 6.71/2.47  
% 6.71/2.47  #Partial instantiations: 0
% 6.71/2.47  #Strategies tried      : 1
% 6.71/2.47  
% 6.71/2.47  Timing (in seconds)
% 6.71/2.47  ----------------------
% 6.71/2.47  Preprocessing        : 0.27
% 6.71/2.47  Parsing              : 0.15
% 6.71/2.47  CNF conversion       : 0.02
% 6.71/2.47  Main loop            : 1.45
% 6.71/2.47  Inferencing          : 0.40
% 6.71/2.47  Reduction            : 0.74
% 6.71/2.47  Demodulation         : 0.62
% 6.71/2.47  BG Simplification    : 0.05
% 6.71/2.47  Subsumption          : 0.19
% 6.71/2.47  Abstraction          : 0.06
% 6.71/2.47  MUC search           : 0.00
% 6.71/2.47  Cooper               : 0.00
% 6.71/2.47  Total                : 1.75
% 6.71/2.47  Index Insertion      : 0.00
% 6.71/2.47  Index Deletion       : 0.00
% 6.71/2.47  Index Matching       : 0.00
% 6.71/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
