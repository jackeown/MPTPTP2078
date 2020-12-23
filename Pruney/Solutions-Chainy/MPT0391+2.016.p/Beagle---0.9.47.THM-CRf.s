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
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_setfam_1(B_9),A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ! [B_10,A_11] :
      ( r1_xboole_0(B_10,A_11)
      | ~ r1_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_67,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_xboole_0(A_20,k4_xboole_0(C_21,B_22))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,'#skF_3')
      | ~ r1_tarski(A_28,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_67])).

tff(c_12,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_111,c_12])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:57:49 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.15  
% 1.61/1.15  %Foreground sorts:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Background operators:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Foreground operators:
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.61/1.15  
% 1.80/1.16  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.80/1.16  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.80/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.80/1.16  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.80/1.16  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.80/1.16  tff(c_16, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.16  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_setfam_1(B_9), A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.80/1.16  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.16  tff(c_17, plain, (![B_10, A_11]: (r1_xboole_0(B_10, A_11) | ~r1_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.16  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_17])).
% 1.80/1.16  tff(c_26, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.16  tff(c_33, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_26])).
% 1.80/1.16  tff(c_67, plain, (![A_20, C_21, B_22]: (r1_xboole_0(A_20, k4_xboole_0(C_21, B_22)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.16  tff(c_111, plain, (![A_28]: (r1_xboole_0(A_28, '#skF_3') | ~r1_tarski(A_28, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_67])).
% 1.80/1.16  tff(c_12, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.16  tff(c_122, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_111, c_12])).
% 1.80/1.16  tff(c_125, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_122])).
% 1.80/1.16  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_125])).
% 1.80/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  Inference rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Ref     : 0
% 1.80/1.16  #Sup     : 30
% 1.80/1.16  #Fact    : 0
% 1.80/1.16  #Define  : 0
% 1.80/1.16  #Split   : 0
% 1.80/1.16  #Chain   : 0
% 1.80/1.16  #Close   : 0
% 1.80/1.16  
% 1.80/1.16  Ordering : KBO
% 1.80/1.16  
% 1.80/1.16  Simplification rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Subsume      : 3
% 1.80/1.16  #Demod        : 2
% 1.80/1.16  #Tautology    : 6
% 1.80/1.16  #SimpNegUnit  : 0
% 1.80/1.16  #BackRed      : 0
% 1.80/1.16  
% 1.80/1.16  #Partial instantiations: 0
% 1.80/1.16  #Strategies tried      : 1
% 1.80/1.16  
% 1.80/1.16  Timing (in seconds)
% 1.80/1.16  ----------------------
% 1.80/1.16  Preprocessing        : 0.26
% 1.80/1.16  Parsing              : 0.15
% 1.80/1.16  CNF conversion       : 0.02
% 1.80/1.16  Main loop            : 0.15
% 1.80/1.16  Inferencing          : 0.06
% 1.80/1.16  Reduction            : 0.04
% 1.80/1.16  Demodulation         : 0.03
% 1.80/1.16  BG Simplification    : 0.01
% 1.80/1.16  Subsumption          : 0.03
% 1.80/1.16  Abstraction          : 0.01
% 1.80/1.16  MUC search           : 0.00
% 1.80/1.16  Cooper               : 0.00
% 1.80/1.16  Total                : 0.44
% 1.80/1.16  Index Insertion      : 0.00
% 1.80/1.16  Index Deletion       : 0.00
% 1.80/1.16  Index Matching       : 0.00
% 1.80/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
