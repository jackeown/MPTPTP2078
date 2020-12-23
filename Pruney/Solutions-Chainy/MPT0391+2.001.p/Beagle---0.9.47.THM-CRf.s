%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_setfam_1(B_10),A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,k3_xboole_0(B_23,C_24))
      | ~ r1_tarski(A_22,C_24)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_303,plain,(
    ! [A_36,A_37,B_38] :
      ( ~ r1_xboole_0(A_36,k3_xboole_0(A_37,B_38))
      | ~ r1_tarski(A_36,A_37)
      | r1_xboole_0(A_36,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_326,plain,(
    ! [A_36] :
      ( ~ r1_xboole_0(A_36,k1_xboole_0)
      | ~ r1_tarski(A_36,'#skF_1')
      | r1_xboole_0(A_36,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_303])).

tff(c_350,plain,(
    ! [A_39] :
      ( ~ r1_tarski(A_39,'#skF_1')
      | r1_xboole_0(A_39,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_326])).

tff(c_14,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_358,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_350,c_14])).

tff(c_361,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:38:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.22  
% 1.93/1.23  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.93/1.23  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.93/1.23  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.93/1.23  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.93/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.93/1.23  tff(f_41, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 1.93/1.23  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.23  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_setfam_1(B_10), A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.23  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.23  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.23  tff(c_53, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.23  tff(c_61, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.93/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.23  tff(c_134, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, k3_xboole_0(B_23, C_24)) | ~r1_tarski(A_22, C_24) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.23  tff(c_303, plain, (![A_36, A_37, B_38]: (~r1_xboole_0(A_36, k3_xboole_0(A_37, B_38)) | ~r1_tarski(A_36, A_37) | r1_xboole_0(A_36, B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_134])).
% 1.93/1.23  tff(c_326, plain, (![A_36]: (~r1_xboole_0(A_36, k1_xboole_0) | ~r1_tarski(A_36, '#skF_1') | r1_xboole_0(A_36, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_303])).
% 1.93/1.23  tff(c_350, plain, (![A_39]: (~r1_tarski(A_39, '#skF_1') | r1_xboole_0(A_39, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_326])).
% 1.93/1.23  tff(c_14, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.23  tff(c_358, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_350, c_14])).
% 1.93/1.23  tff(c_361, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_358])).
% 1.93/1.23  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_361])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 80
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 0
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 10
% 1.93/1.23  #Demod        : 24
% 1.93/1.23  #Tautology    : 40
% 1.93/1.23  #SimpNegUnit  : 0
% 1.93/1.23  #BackRed      : 0
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.23  Preprocessing        : 0.25
% 1.93/1.23  Parsing              : 0.14
% 1.93/1.23  CNF conversion       : 0.01
% 1.93/1.23  Main loop            : 0.21
% 1.93/1.23  Inferencing          : 0.08
% 1.93/1.23  Reduction            : 0.07
% 1.93/1.23  Demodulation         : 0.05
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.04
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.49
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
