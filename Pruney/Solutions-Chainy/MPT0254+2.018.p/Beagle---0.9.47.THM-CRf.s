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
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_90,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ r1_tarski(A_47,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_90])).

tff(c_106,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [D_22,B_18] : r2_hidden(D_22,k2_tarski(D_22,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [D_22,B_18] : ~ v1_xboole_0(k2_tarski(D_22,B_18)) ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_123,plain,(
    ! [A_49] : ~ v1_xboole_0(k1_tarski(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_87])).

tff(c_125,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_123])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.69/1.17  
% 1.69/1.17  %Foreground sorts:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Background operators:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Foreground operators:
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.69/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.69/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.17  
% 1.69/1.17  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.69/1.17  tff(f_83, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.69/1.17  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.17  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.69/1.17  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.69/1.17  tff(f_69, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.69/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.69/1.17  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.69/1.17  tff(c_68, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.17  tff(c_71, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_68])).
% 1.69/1.17  tff(c_90, plain, (![A_47]: (k1_xboole_0=A_47 | ~r1_tarski(A_47, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.17  tff(c_94, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_90])).
% 1.69/1.17  tff(c_106, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.69/1.17  tff(c_30, plain, (![D_22, B_18]: (r2_hidden(D_22, k2_tarski(D_22, B_18)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.17  tff(c_80, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.17  tff(c_87, plain, (![D_22, B_18]: (~v1_xboole_0(k2_tarski(D_22, B_18)))), inference(resolution, [status(thm)], [c_30, c_80])).
% 1.69/1.17  tff(c_123, plain, (![A_49]: (~v1_xboole_0(k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_87])).
% 1.69/1.17  tff(c_125, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_123])).
% 1.69/1.17  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_125])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 18
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 0
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.18  Ordering : KBO
% 1.69/1.18  
% 1.69/1.18  Simplification rules
% 1.69/1.18  ----------------------
% 1.69/1.18  #Subsume      : 1
% 1.69/1.18  #Demod        : 3
% 1.69/1.18  #Tautology    : 10
% 1.69/1.18  #SimpNegUnit  : 0
% 1.69/1.18  #BackRed      : 2
% 1.69/1.18  
% 1.69/1.18  #Partial instantiations: 0
% 1.69/1.18  #Strategies tried      : 1
% 1.69/1.18  
% 1.69/1.18  Timing (in seconds)
% 1.69/1.18  ----------------------
% 1.69/1.18  Preprocessing        : 0.31
% 1.69/1.18  Parsing              : 0.16
% 1.69/1.18  CNF conversion       : 0.02
% 1.69/1.18  Main loop            : 0.11
% 1.69/1.18  Inferencing          : 0.03
% 1.69/1.18  Reduction            : 0.04
% 1.69/1.18  Demodulation         : 0.03
% 1.69/1.18  BG Simplification    : 0.01
% 1.69/1.18  Subsumption          : 0.02
% 1.69/1.18  Abstraction          : 0.01
% 1.69/1.18  MUC search           : 0.00
% 1.69/1.18  Cooper               : 0.00
% 1.69/1.18  Total                : 0.45
% 1.69/1.18  Index Insertion      : 0.00
% 1.69/1.18  Index Deletion       : 0.00
% 1.69/1.18  Index Matching       : 0.00
% 1.69/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
