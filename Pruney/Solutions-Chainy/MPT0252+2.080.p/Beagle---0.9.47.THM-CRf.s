%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,C_35)
      | ~ r1_tarski(k2_tarski(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    ! [A_34,B_36] : r2_hidden(A_34,k2_tarski(A_34,B_36)) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_43])).

tff(c_104,plain,(
    ! [D_39,A_40,B_41] :
      ( ~ r2_hidden(D_39,A_40)
      | r2_hidden(D_39,k2_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'))
      | r2_hidden(D_47,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_104])).

tff(c_148,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_5')
      | ~ r2_hidden(D_48,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_152,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_148])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.94/1.21  
% 1.94/1.21  %Foreground sorts:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Background operators:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Foreground operators:
% 1.94/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.21  
% 1.94/1.22  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.94/1.22  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.22  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.94/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.94/1.22  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.94/1.22  tff(c_38, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.22  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.22  tff(c_97, plain, (![A_34, C_35, B_36]: (r2_hidden(A_34, C_35) | ~r1_tarski(k2_tarski(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.22  tff(c_102, plain, (![A_34, B_36]: (r2_hidden(A_34, k2_tarski(A_34, B_36)))), inference(resolution, [status(thm)], [c_24, c_97])).
% 1.94/1.22  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.94/1.22  tff(c_40, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.22  tff(c_43, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.22  tff(c_50, plain, (k2_xboole_0(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_40, c_43])).
% 1.94/1.22  tff(c_104, plain, (![D_39, A_40, B_41]: (~r2_hidden(D_39, A_40) | r2_hidden(D_39, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.94/1.22  tff(c_137, plain, (![D_47]: (~r2_hidden(D_47, k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')) | r2_hidden(D_47, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_104])).
% 1.94/1.22  tff(c_148, plain, (![D_48]: (r2_hidden(D_48, '#skF_5') | ~r2_hidden(D_48, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_6, c_137])).
% 1.94/1.22  tff(c_152, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_102, c_148])).
% 1.94/1.22  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_152])).
% 1.94/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  Inference rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Ref     : 0
% 1.94/1.22  #Sup     : 26
% 1.94/1.22  #Fact    : 0
% 1.94/1.22  #Define  : 0
% 1.94/1.22  #Split   : 0
% 1.94/1.22  #Chain   : 0
% 1.94/1.22  #Close   : 0
% 1.94/1.22  
% 1.94/1.22  Ordering : KBO
% 1.94/1.22  
% 1.94/1.22  Simplification rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Subsume      : 0
% 1.94/1.22  #Demod        : 2
% 1.94/1.22  #Tautology    : 16
% 1.94/1.22  #SimpNegUnit  : 1
% 1.94/1.22  #BackRed      : 0
% 1.94/1.22  
% 1.94/1.22  #Partial instantiations: 0
% 1.94/1.22  #Strategies tried      : 1
% 1.94/1.22  
% 1.94/1.22  Timing (in seconds)
% 1.94/1.22  ----------------------
% 1.94/1.22  Preprocessing        : 0.31
% 1.94/1.22  Parsing              : 0.16
% 1.94/1.22  CNF conversion       : 0.02
% 1.94/1.22  Main loop            : 0.14
% 1.94/1.22  Inferencing          : 0.05
% 1.94/1.22  Reduction            : 0.04
% 1.94/1.22  Demodulation         : 0.03
% 1.94/1.22  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.03
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.48
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
