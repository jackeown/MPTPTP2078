%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8,c_11])).

tff(c_20,plain,(
    ! [C_8,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_8,A_9),B_10) = k7_relat_1(C_8,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_15,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:28:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.14  
% 1.66/1.14  %Foreground sorts:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Background operators:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Foreground operators:
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.14  
% 1.66/1.15  tff(f_40, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.66/1.15  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.66/1.15  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.66/1.15  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.15  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.15  tff(c_11, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.15  tff(c_15, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_8, c_11])).
% 1.66/1.15  tff(c_20, plain, (![C_8, A_9, B_10]: (k7_relat_1(k7_relat_1(C_8, A_9), B_10)=k7_relat_1(C_8, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.15  tff(c_6, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.15  tff(c_29, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_6])).
% 1.66/1.15  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_15, c_29])).
% 1.66/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  Inference rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Ref     : 0
% 1.66/1.15  #Sup     : 8
% 1.66/1.15  #Fact    : 0
% 1.66/1.15  #Define  : 0
% 1.66/1.15  #Split   : 0
% 1.66/1.15  #Chain   : 0
% 1.66/1.15  #Close   : 0
% 1.66/1.15  
% 1.66/1.15  Ordering : KBO
% 1.66/1.15  
% 1.66/1.15  Simplification rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Subsume      : 0
% 1.66/1.15  #Demod        : 2
% 1.66/1.15  #Tautology    : 3
% 1.66/1.15  #SimpNegUnit  : 0
% 1.66/1.15  #BackRed      : 0
% 1.66/1.15  
% 1.66/1.15  #Partial instantiations: 0
% 1.66/1.15  #Strategies tried      : 1
% 1.66/1.15  
% 1.66/1.15  Timing (in seconds)
% 1.66/1.15  ----------------------
% 1.66/1.15  Preprocessing        : 0.27
% 1.66/1.15  Parsing              : 0.15
% 1.66/1.15  CNF conversion       : 0.02
% 1.66/1.15  Main loop            : 0.08
% 1.66/1.15  Inferencing          : 0.04
% 1.66/1.15  Reduction            : 0.02
% 1.66/1.15  Demodulation         : 0.01
% 1.66/1.15  BG Simplification    : 0.01
% 1.66/1.15  Subsumption          : 0.01
% 1.66/1.15  Abstraction          : 0.00
% 1.66/1.15  MUC search           : 0.00
% 1.66/1.15  Cooper               : 0.00
% 1.66/1.15  Total                : 0.36
% 1.66/1.15  Index Insertion      : 0.00
% 1.66/1.15  Index Deletion       : 0.00
% 1.66/1.15  Index Matching       : 0.00
% 1.66/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
