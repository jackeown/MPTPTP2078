%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:45 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | ~ r1_tarski(k1_tarski(A_31),B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_31,B_10] : r2_hidden(A_31,k2_xboole_0(k1_tarski(A_31),B_10)) ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_148,plain,(
    ! [D_39,A_40,B_41] :
      ( ~ r2_hidden(D_39,A_40)
      | r2_hidden(D_39,k2_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_247,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'))
      | r2_hidden(D_46,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_148])).

tff(c_262,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_247])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.19  
% 1.91/1.19  tff(f_55, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.91/1.19  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.91/1.19  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.91/1.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.91/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.91/1.19  tff(c_34, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.19  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.19  tff(c_119, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | ~r1_tarski(k1_tarski(A_31), B_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.19  tff(c_133, plain, (![A_31, B_10]: (r2_hidden(A_31, k2_xboole_0(k1_tarski(A_31), B_10)))), inference(resolution, [status(thm)], [c_22, c_119])).
% 1.91/1.19  tff(c_36, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.19  tff(c_48, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.19  tff(c_59, plain, (k2_xboole_0(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_48])).
% 1.91/1.19  tff(c_148, plain, (![D_39, A_40, B_41]: (~r2_hidden(D_39, A_40) | r2_hidden(D_39, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.19  tff(c_247, plain, (![D_46]: (~r2_hidden(D_46, k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(D_46, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_148])).
% 1.91/1.19  tff(c_262, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_133, c_247])).
% 1.91/1.19  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_262])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 55
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 5
% 1.91/1.19  #Demod        : 13
% 1.91/1.19  #Tautology    : 33
% 1.91/1.19  #SimpNegUnit  : 1
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.20  Preprocessing        : 0.28
% 1.91/1.20  Parsing              : 0.14
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.16
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.05
% 1.91/1.20  Demodulation         : 0.04
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.46
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
