%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(k4_tarski('#skF_1'(A_28,B_29),'#skF_2'(A_28,B_29)),A_28)
      | r1_tarski(A_28,B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_22,C_23] : ~ r2_hidden(k4_tarski(B_22,C_23),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ! [B_29] :
      ( r1_tarski('#skF_3',B_29)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_17,c_12])).

tff(c_31,plain,(
    ! [B_32] : r1_tarski('#skF_3',B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_31,c_2])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:44:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.51/1.07  
% 1.51/1.07  %Foreground sorts:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Background operators:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Foreground operators:
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.51/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.51/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.51/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.51/1.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.51/1.07  
% 1.51/1.08  tff(f_48, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.51/1.08  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.51/1.08  tff(f_29, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.51/1.08  tff(c_10, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.51/1.08  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.51/1.08  tff(c_17, plain, (![A_28, B_29]: (r2_hidden(k4_tarski('#skF_1'(A_28, B_29), '#skF_2'(A_28, B_29)), A_28) | r1_tarski(A_28, B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.51/1.08  tff(c_12, plain, (![B_22, C_23]: (~r2_hidden(k4_tarski(B_22, C_23), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.51/1.08  tff(c_21, plain, (![B_29]: (r1_tarski('#skF_3', B_29) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_17, c_12])).
% 1.51/1.08  tff(c_31, plain, (![B_32]: (r1_tarski('#skF_3', B_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21])).
% 1.51/1.08  tff(c_2, plain, (![A_1, B_2]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k4_xboole_0(B_2, A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.08  tff(c_35, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_31, c_2])).
% 1.51/1.08  tff(c_39, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_35])).
% 1.51/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.08  
% 1.51/1.08  Inference rules
% 1.51/1.08  ----------------------
% 1.51/1.08  #Ref     : 0
% 1.51/1.08  #Sup     : 3
% 1.51/1.08  #Fact    : 0
% 1.51/1.08  #Define  : 0
% 1.51/1.08  #Split   : 0
% 1.51/1.08  #Chain   : 0
% 1.51/1.08  #Close   : 0
% 1.51/1.08  
% 1.51/1.08  Ordering : KBO
% 1.51/1.08  
% 1.51/1.08  Simplification rules
% 1.51/1.08  ----------------------
% 1.51/1.08  #Subsume      : 0
% 1.51/1.08  #Demod        : 1
% 1.51/1.08  #Tautology    : 0
% 1.51/1.08  #SimpNegUnit  : 1
% 1.51/1.08  #BackRed      : 0
% 1.51/1.08  
% 1.51/1.08  #Partial instantiations: 0
% 1.51/1.08  #Strategies tried      : 1
% 1.51/1.08  
% 1.51/1.08  Timing (in seconds)
% 1.51/1.08  ----------------------
% 1.51/1.08  Preprocessing        : 0.26
% 1.51/1.08  Parsing              : 0.14
% 1.51/1.08  CNF conversion       : 0.02
% 1.51/1.08  Main loop            : 0.07
% 1.51/1.08  Inferencing          : 0.03
% 1.51/1.09  Reduction            : 0.02
% 1.51/1.09  Demodulation         : 0.01
% 1.51/1.09  BG Simplification    : 0.01
% 1.51/1.09  Subsumption          : 0.01
% 1.51/1.09  Abstraction          : 0.00
% 1.51/1.09  MUC search           : 0.00
% 1.51/1.09  Cooper               : 0.00
% 1.51/1.09  Total                : 0.35
% 1.51/1.09  Index Insertion      : 0.00
% 1.51/1.09  Index Deletion       : 0.00
% 1.51/1.09  Index Matching       : 0.00
% 1.51/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
