%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  60 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_tarski(B_12,k1_setfam_1(A_11))
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_51,plain,(
    ! [D_18,B_19,A_20] :
      ( r2_hidden(D_18,B_19)
      | ~ r2_hidden(D_18,k3_xboole_0(A_20,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_5')
      | ~ r2_hidden(D_18,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_setfam_1(B_10),A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [B_33,A_34] :
      ( ~ r1_tarski(B_33,'#skF_3'(A_34,B_33))
      | r1_tarski(B_33,k1_setfam_1(A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k1_setfam_1(B_37),k1_setfam_1(A_38))
      | k1_xboole_0 = A_38
      | ~ r2_hidden('#skF_3'(A_38,k1_setfam_1(B_37)),B_37) ) ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_163,plain,(
    ! [A_41] :
      ( r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1(A_41))
      | k1_xboole_0 = A_41
      | ~ r2_hidden('#skF_3'(A_41,k1_setfam_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_167,plain,
    ( r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_30,c_28,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.93/1.27  
% 1.93/1.27  %Foreground sorts:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Background operators:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Foreground operators:
% 1.93/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.27  
% 2.03/1.28  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.03/1.28  tff(f_51, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.03/1.28  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.28  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.03/1.28  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.03/1.28  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.28  tff(c_28, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.28  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_tarski(B_12, k1_setfam_1(A_11)) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.28  tff(c_32, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.28  tff(c_38, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.28  tff(c_46, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.03/1.28  tff(c_51, plain, (![D_18, B_19, A_20]: (r2_hidden(D_18, B_19) | ~r2_hidden(D_18, k3_xboole_0(A_20, B_19)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.28  tff(c_54, plain, (![D_18]: (r2_hidden(D_18, '#skF_5') | ~r2_hidden(D_18, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 2.03/1.28  tff(c_22, plain, (![B_10, A_9]: (r1_tarski(k1_setfam_1(B_10), A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.28  tff(c_95, plain, (![B_33, A_34]: (~r1_tarski(B_33, '#skF_3'(A_34, B_33)) | r1_tarski(B_33, k1_setfam_1(A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.28  tff(c_115, plain, (![B_37, A_38]: (r1_tarski(k1_setfam_1(B_37), k1_setfam_1(A_38)) | k1_xboole_0=A_38 | ~r2_hidden('#skF_3'(A_38, k1_setfam_1(B_37)), B_37))), inference(resolution, [status(thm)], [c_22, c_95])).
% 2.03/1.28  tff(c_163, plain, (![A_41]: (r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1(A_41)) | k1_xboole_0=A_41 | ~r2_hidden('#skF_3'(A_41, k1_setfam_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_115])).
% 2.03/1.28  tff(c_167, plain, (r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_163])).
% 2.03/1.28  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_30, c_28, c_167])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 32
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 0
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 0
% 2.03/1.28  #Demod        : 0
% 2.03/1.28  #Tautology    : 17
% 2.03/1.28  #SimpNegUnit  : 1
% 2.03/1.28  #BackRed      : 0
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.28  Preprocessing        : 0.32
% 2.03/1.28  Parsing              : 0.17
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.15
% 2.03/1.28  Inferencing          : 0.06
% 2.03/1.28  Reduction            : 0.04
% 2.03/1.28  Demodulation         : 0.02
% 2.03/1.28  BG Simplification    : 0.02
% 2.03/1.28  Subsumption          : 0.03
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.49
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
