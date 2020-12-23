%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k1_tarski(A_7),k2_tarski(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_xboole_0(A_15,C_16)
      | ~ r1_xboole_0(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_18] :
      ( r1_xboole_0(A_18,'#skF_3')
      | ~ r1_tarski(A_18,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_28])).

tff(c_37,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_32])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden(A_5,B_6)
      | ~ r1_xboole_0(k1_tarski(A_5),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_6])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.56/1.07  
% 1.56/1.07  %Foreground sorts:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Background operators:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Foreground operators:
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.56/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.56/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.56/1.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.56/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.07  
% 1.56/1.08  tff(f_46, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.56/1.08  tff(f_40, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.56/1.08  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.56/1.08  tff(f_38, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.56/1.08  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.56/1.08  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.08  tff(c_12, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.56/1.08  tff(c_28, plain, (![A_15, C_16, B_17]: (r1_xboole_0(A_15, C_16) | ~r1_xboole_0(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.08  tff(c_32, plain, (![A_18]: (r1_xboole_0(A_18, '#skF_3') | ~r1_tarski(A_18, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_28])).
% 1.56/1.08  tff(c_37, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_32])).
% 1.56/1.08  tff(c_6, plain, (![A_5, B_6]: (~r2_hidden(A_5, B_6) | ~r1_xboole_0(k1_tarski(A_5), B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.08  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_37, c_6])).
% 1.56/1.08  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 1.56/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.08  
% 1.56/1.08  Inference rules
% 1.56/1.08  ----------------------
% 1.56/1.08  #Ref     : 0
% 1.56/1.08  #Sup     : 7
% 1.56/1.08  #Fact    : 0
% 1.56/1.08  #Define  : 0
% 1.56/1.08  #Split   : 0
% 1.56/1.08  #Chain   : 0
% 1.56/1.08  #Close   : 0
% 1.56/1.08  
% 1.56/1.08  Ordering : KBO
% 1.56/1.08  
% 1.56/1.08  Simplification rules
% 1.56/1.08  ----------------------
% 1.56/1.08  #Subsume      : 0
% 1.56/1.08  #Demod        : 1
% 1.56/1.08  #Tautology    : 2
% 1.56/1.08  #SimpNegUnit  : 0
% 1.56/1.08  #BackRed      : 0
% 1.56/1.08  
% 1.56/1.08  #Partial instantiations: 0
% 1.56/1.08  #Strategies tried      : 1
% 1.56/1.08  
% 1.56/1.08  Timing (in seconds)
% 1.56/1.08  ----------------------
% 1.56/1.08  Preprocessing        : 0.26
% 1.56/1.08  Parsing              : 0.14
% 1.56/1.08  CNF conversion       : 0.01
% 1.56/1.08  Main loop            : 0.07
% 1.56/1.08  Inferencing          : 0.03
% 1.56/1.08  Reduction            : 0.02
% 1.56/1.08  Demodulation         : 0.02
% 1.56/1.08  BG Simplification    : 0.01
% 1.56/1.08  Subsumption          : 0.01
% 1.56/1.08  Abstraction          : 0.01
% 1.56/1.08  MUC search           : 0.00
% 1.56/1.08  Cooper               : 0.00
% 1.56/1.08  Total                : 0.36
% 1.56/1.08  Index Insertion      : 0.00
% 1.56/1.08  Index Deletion       : 0.00
% 1.63/1.08  Index Matching       : 0.00
% 1.63/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
