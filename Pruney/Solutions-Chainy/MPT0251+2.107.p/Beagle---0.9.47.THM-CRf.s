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
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(k1_tarski(A_17),B_18) = B_18
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_10,c_39])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.08  
% 1.51/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.08  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.51/1.08  
% 1.51/1.08  %Foreground sorts:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Background operators:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Foreground operators:
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.51/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.51/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.51/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.51/1.09  
% 1.51/1.09  tff(f_42, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.51/1.09  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.51/1.09  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.51/1.09  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.09  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.51/1.09  tff(c_39, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.09  tff(c_44, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)=B_18 | ~r2_hidden(A_17, B_18))), inference(resolution, [status(thm)], [c_10, c_39])).
% 1.51/1.09  tff(c_12, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.09  tff(c_50, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_12])).
% 1.51/1.09  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 1.51/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.09  
% 1.51/1.09  Inference rules
% 1.51/1.09  ----------------------
% 1.51/1.09  #Ref     : 0
% 1.51/1.09  #Sup     : 9
% 1.51/1.09  #Fact    : 0
% 1.51/1.09  #Define  : 0
% 1.51/1.09  #Split   : 0
% 1.51/1.09  #Chain   : 0
% 1.51/1.09  #Close   : 0
% 1.51/1.09  
% 1.51/1.09  Ordering : KBO
% 1.51/1.09  
% 1.51/1.09  Simplification rules
% 1.51/1.09  ----------------------
% 1.51/1.09  #Subsume      : 0
% 1.51/1.09  #Demod        : 1
% 1.51/1.09  #Tautology    : 6
% 1.51/1.09  #SimpNegUnit  : 0
% 1.51/1.09  #BackRed      : 0
% 1.51/1.09  
% 1.51/1.09  #Partial instantiations: 0
% 1.51/1.09  #Strategies tried      : 1
% 1.51/1.09  
% 1.51/1.09  Timing (in seconds)
% 1.51/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.27
% 1.63/1.09  Parsing              : 0.14
% 1.63/1.09  CNF conversion       : 0.01
% 1.63/1.09  Main loop            : 0.07
% 1.63/1.09  Inferencing          : 0.03
% 1.63/1.10  Reduction            : 0.02
% 1.63/1.10  Demodulation         : 0.01
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.01
% 1.63/1.10  Abstraction          : 0.01
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.36
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
