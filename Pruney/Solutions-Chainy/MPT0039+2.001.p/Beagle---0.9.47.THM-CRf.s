%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  85 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_126,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,k4_xboole_0(A_38,B_39))
      | r2_hidden(D_37,B_39)
      | ~ r2_hidden(D_37,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [D_23,B_24,A_25] :
      ( ~ r2_hidden(D_23,B_24)
      | ~ r2_hidden(D_23,k4_xboole_0(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [D_23] :
      ( ~ r2_hidden(D_23,'#skF_4')
      | ~ r2_hidden(D_23,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_156,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_5')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_126,c_78])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_176,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_44,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_156,c_6])).

tff(c_181,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_181,c_28])).

tff(c_186,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,k4_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden(D_45,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_126])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_220,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,'#skF_4')
      | ~ r2_hidden(D_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_230,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_1'('#skF_5',B_47),'#skF_4')
      | r1_tarski('#skF_5',B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_244,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_248,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_244,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_311,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2])).

tff(c_323,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_311])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.22  
% 2.08/1.23  tff(f_53, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 2.08/1.23  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.23  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.08/1.23  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.23  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.23  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.23  tff(c_126, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, k4_xboole_0(A_38, B_39)) | r2_hidden(D_37, B_39) | ~r2_hidden(D_37, A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.23  tff(c_32, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.23  tff(c_75, plain, (![D_23, B_24, A_25]: (~r2_hidden(D_23, B_24) | ~r2_hidden(D_23, k4_xboole_0(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.23  tff(c_78, plain, (![D_23]: (~r2_hidden(D_23, '#skF_4') | ~r2_hidden(D_23, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_75])).
% 2.08/1.23  tff(c_156, plain, (![D_40]: (r2_hidden(D_40, '#skF_5') | ~r2_hidden(D_40, '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_78])).
% 2.08/1.23  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.23  tff(c_176, plain, (![A_44]: (r1_tarski(A_44, '#skF_5') | ~r2_hidden('#skF_1'(A_44, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_156, c_6])).
% 2.08/1.23  tff(c_181, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_176])).
% 2.08/1.23  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.23  tff(c_185, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_181, c_28])).
% 2.08/1.23  tff(c_186, plain, (![D_45]: (r2_hidden(D_45, k4_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_45, '#skF_4') | ~r2_hidden(D_45, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_126])).
% 2.08/1.23  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.23  tff(c_220, plain, (![D_46]: (r2_hidden(D_46, '#skF_4') | ~r2_hidden(D_46, '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_12])).
% 2.08/1.23  tff(c_230, plain, (![B_47]: (r2_hidden('#skF_1'('#skF_5', B_47), '#skF_4') | r1_tarski('#skF_5', B_47))), inference(resolution, [status(thm)], [c_8, c_220])).
% 2.08/1.23  tff(c_244, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_230, c_6])).
% 2.08/1.23  tff(c_248, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_244, c_28])).
% 2.08/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.23  tff(c_311, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_248, c_2])).
% 2.08/1.23  tff(c_323, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_311])).
% 2.08/1.23  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_323])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 67
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 3
% 2.08/1.23  #Demod        : 2
% 2.08/1.23  #Tautology    : 21
% 2.08/1.23  #SimpNegUnit  : 1
% 2.08/1.23  #BackRed      : 0
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.27
% 2.08/1.23  Parsing              : 0.14
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.20
% 2.08/1.23  Inferencing          : 0.08
% 2.08/1.23  Reduction            : 0.06
% 2.08/1.23  Demodulation         : 0.04
% 2.08/1.24  BG Simplification    : 0.02
% 2.08/1.24  Subsumption          : 0.05
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.51
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
