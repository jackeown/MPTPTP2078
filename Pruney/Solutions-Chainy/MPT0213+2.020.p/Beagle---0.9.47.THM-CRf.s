%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  51 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_277,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_3'(A_73,B_74),A_73)
      | r2_hidden('#skF_4'(A_73,B_74),B_74)
      | k3_tarski(A_73) = B_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),B_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_43,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [B_39] : k3_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [B_39,C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,B_39)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_84,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_79])).

tff(c_391,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_75),B_75)
      | k3_tarski(k1_xboole_0) = B_75 ) ),
    inference(resolution,[status(thm)],[c_277,c_84])).

tff(c_433,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_84])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.72/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.72/1.16  
% 1.72/1.17  tff(f_57, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.72/1.17  tff(f_55, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.72/1.17  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.72/1.17  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.72/1.17  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.72/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.72/1.17  tff(c_30, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_277, plain, (![A_73, B_74]: (r2_hidden('#skF_3'(A_73, B_74), A_73) | r2_hidden('#skF_4'(A_73, B_74), B_74) | k3_tarski(A_73)=B_74)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.17  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.17  tff(c_38, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.17  tff(c_41, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 1.72/1.17  tff(c_43, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.17  tff(c_74, plain, (![B_39]: (k3_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43, c_8])).
% 1.72/1.17  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.17  tff(c_79, plain, (![B_39, C_5]: (~r1_xboole_0(k1_xboole_0, B_39) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 1.72/1.17  tff(c_84, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_79])).
% 1.72/1.17  tff(c_391, plain, (![B_75]: (r2_hidden('#skF_4'(k1_xboole_0, B_75), B_75) | k3_tarski(k1_xboole_0)=B_75)), inference(resolution, [status(thm)], [c_277, c_84])).
% 1.72/1.17  tff(c_433, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_391, c_84])).
% 1.72/1.17  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_433])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 89
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 2
% 1.72/1.17  #Demod        : 37
% 1.72/1.17  #Tautology    : 27
% 1.72/1.17  #SimpNegUnit  : 2
% 1.72/1.17  #BackRed      : 0
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.72/1.17  Preprocessing        : 0.28
% 1.72/1.17  Parsing              : 0.15
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.22
% 1.72/1.17  Inferencing          : 0.08
% 1.72/1.17  Reduction            : 0.06
% 1.72/1.17  Demodulation         : 0.04
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.04
% 1.72/1.17  Abstraction          : 0.01
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.52
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
