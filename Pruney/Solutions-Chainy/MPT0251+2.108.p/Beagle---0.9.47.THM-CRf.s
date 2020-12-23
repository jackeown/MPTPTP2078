%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_6,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(k1_tarski(A_3),B_4) = B_4
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7,c_4])).

tff(c_21,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.02  
% 1.46/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.03  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.46/1.03  
% 1.46/1.03  %Foreground sorts:
% 1.46/1.03  
% 1.46/1.03  
% 1.46/1.03  %Background operators:
% 1.46/1.03  
% 1.46/1.03  
% 1.46/1.03  %Foreground operators:
% 1.46/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.46/1.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.46/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.46/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.46/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.46/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.46/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.46/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.46/1.03  
% 1.46/1.04  tff(f_34, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.46/1.04  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.46/1.04  tff(c_6, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.46/1.04  tff(c_7, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), B_4)=B_4 | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.46/1.04  tff(c_4, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.46/1.04  tff(c_13, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7, c_4])).
% 1.46/1.04  tff(c_21, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13])).
% 1.46/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.04  
% 1.46/1.04  Inference rules
% 1.46/1.04  ----------------------
% 1.46/1.04  #Ref     : 0
% 1.46/1.04  #Sup     : 3
% 1.46/1.04  #Fact    : 0
% 1.46/1.04  #Define  : 0
% 1.46/1.04  #Split   : 0
% 1.46/1.04  #Chain   : 0
% 1.46/1.04  #Close   : 0
% 1.46/1.04  
% 1.46/1.04  Ordering : KBO
% 1.46/1.04  
% 1.46/1.04  Simplification rules
% 1.46/1.04  ----------------------
% 1.46/1.04  #Subsume      : 0
% 1.46/1.04  #Demod        : 1
% 1.46/1.04  #Tautology    : 1
% 1.46/1.04  #SimpNegUnit  : 0
% 1.46/1.04  #BackRed      : 0
% 1.46/1.04  
% 1.46/1.04  #Partial instantiations: 0
% 1.46/1.04  #Strategies tried      : 1
% 1.46/1.04  
% 1.46/1.04  Timing (in seconds)
% 1.46/1.04  ----------------------
% 1.46/1.04  Preprocessing        : 0.23
% 1.46/1.04  Parsing              : 0.13
% 1.46/1.04  CNF conversion       : 0.01
% 1.46/1.04  Main loop            : 0.05
% 1.46/1.04  Inferencing          : 0.02
% 1.46/1.04  Reduction            : 0.01
% 1.46/1.04  Demodulation         : 0.01
% 1.46/1.04  BG Simplification    : 0.00
% 1.46/1.04  Subsumption          : 0.00
% 1.46/1.04  Abstraction          : 0.00
% 1.46/1.04  MUC search           : 0.00
% 1.46/1.04  Cooper               : 0.00
% 1.46/1.04  Total                : 0.31
% 1.46/1.04  Index Insertion      : 0.00
% 1.46/1.04  Index Deletion       : 0.00
% 1.46/1.04  Index Matching       : 0.00
% 1.46/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
