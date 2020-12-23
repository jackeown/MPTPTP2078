%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:04 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  39 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_36,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k7_relat_1(B_43,A_44),B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_44] :
      ( k7_relat_1(k1_xboole_0,A_44) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_42,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_18,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_45,C_46,B_47] :
      ( ~ r2_hidden(A_45,C_46)
      | ~ r1_xboole_0(k2_tarski(A_45,B_47),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_48] : ~ r2_hidden(A_48,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_53])).

tff(c_58,plain,(
    ! [A_44] : k7_relat_1(k1_xboole_0,A_44) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_22,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.19  
% 1.71/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.71/1.20  
% 1.71/1.20  %Foreground sorts:
% 1.71/1.20  
% 1.71/1.20  
% 1.71/1.20  %Background operators:
% 1.71/1.20  
% 1.71/1.20  
% 1.71/1.20  %Foreground operators:
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.71/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.71/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.20  
% 1.71/1.21  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.71/1.21  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.71/1.21  tff(f_52, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.71/1.21  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.71/1.21  tff(f_42, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.71/1.21  tff(f_59, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.71/1.21  tff(c_36, plain, (![B_43, A_44]: (r1_tarski(k7_relat_1(B_43, A_44), B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.21  tff(c_41, plain, (![A_44]: (k7_relat_1(k1_xboole_0, A_44)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.71/1.21  tff(c_42, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_41])).
% 1.71/1.21  tff(c_18, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.71/1.21  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.21  tff(c_43, plain, (![A_45, C_46, B_47]: (~r2_hidden(A_45, C_46) | ~r1_xboole_0(k2_tarski(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.21  tff(c_49, plain, (![A_48]: (~r2_hidden(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_43])).
% 1.71/1.21  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_49])).
% 1.71/1.21  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_53])).
% 1.71/1.21  tff(c_58, plain, (![A_44]: (k7_relat_1(k1_xboole_0, A_44)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_41])).
% 1.71/1.21  tff(c_22, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.21  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 1.71/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.21  
% 1.71/1.21  Inference rules
% 1.71/1.21  ----------------------
% 1.71/1.21  #Ref     : 0
% 1.71/1.21  #Sup     : 5
% 1.71/1.21  #Fact    : 0
% 1.71/1.21  #Define  : 0
% 1.71/1.21  #Split   : 1
% 1.71/1.21  #Chain   : 0
% 1.71/1.21  #Close   : 0
% 1.71/1.21  
% 1.71/1.21  Ordering : KBO
% 1.71/1.21  
% 1.71/1.21  Simplification rules
% 1.71/1.21  ----------------------
% 1.71/1.21  #Subsume      : 0
% 1.71/1.21  #Demod        : 1
% 1.71/1.21  #Tautology    : 2
% 1.71/1.21  #SimpNegUnit  : 1
% 1.71/1.21  #BackRed      : 1
% 1.71/1.21  
% 1.71/1.21  #Partial instantiations: 0
% 1.71/1.21  #Strategies tried      : 1
% 1.71/1.21  
% 1.71/1.21  Timing (in seconds)
% 1.71/1.21  ----------------------
% 1.71/1.21  Preprocessing        : 0.28
% 1.71/1.21  Parsing              : 0.15
% 1.71/1.21  CNF conversion       : 0.02
% 1.71/1.21  Main loop            : 0.13
% 1.71/1.21  Inferencing          : 0.06
% 1.71/1.21  Reduction            : 0.04
% 1.71/1.21  Demodulation         : 0.02
% 1.71/1.21  BG Simplification    : 0.01
% 1.71/1.21  Subsumption          : 0.01
% 1.71/1.21  Abstraction          : 0.01
% 1.71/1.21  MUC search           : 0.00
% 1.71/1.21  Cooper               : 0.00
% 1.71/1.21  Total                : 0.43
% 1.71/1.21  Index Insertion      : 0.00
% 1.71/1.21  Index Deletion       : 0.00
% 1.71/1.21  Index Matching       : 0.00
% 1.71/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
