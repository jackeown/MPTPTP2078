%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  34 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(k4_tarski('#skF_1'(A_34,B_35),'#skF_2'(A_34,B_35)),A_34)
      | r1_tarski(A_34,B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_23,C_24] : ~ r2_hidden(k4_tarski(B_23,C_24),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57,plain,(
    ! [B_35] :
      ( r1_tarski('#skF_3',B_35)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_18])).

tff(c_63,plain,(
    ! [B_36] : r1_tarski('#skF_3',B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_57])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_63,c_30])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.40  
% 1.94/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.40  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.94/1.40  
% 1.94/1.40  %Foreground sorts:
% 1.94/1.40  
% 1.94/1.40  
% 1.94/1.40  %Background operators:
% 1.94/1.40  
% 1.94/1.40  
% 1.94/1.40  %Foreground operators:
% 1.94/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.40  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.40  
% 1.94/1.42  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.94/1.42  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.94/1.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.42  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.42  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.42  tff(c_49, plain, (![A_34, B_35]: (r2_hidden(k4_tarski('#skF_1'(A_34, B_35), '#skF_2'(A_34, B_35)), A_34) | r1_tarski(A_34, B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.42  tff(c_18, plain, (![B_23, C_24]: (~r2_hidden(k4_tarski(B_23, C_24), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.42  tff(c_57, plain, (![B_35]: (r1_tarski('#skF_3', B_35) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_49, c_18])).
% 1.94/1.42  tff(c_63, plain, (![B_36]: (r1_tarski('#skF_3', B_36))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_57])).
% 1.94/1.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.42  tff(c_25, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.42  tff(c_30, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_25])).
% 1.94/1.42  tff(c_67, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_63, c_30])).
% 1.94/1.42  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_67])).
% 1.94/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.42  
% 1.94/1.42  Inference rules
% 1.94/1.42  ----------------------
% 1.94/1.42  #Ref     : 0
% 1.94/1.42  #Sup     : 8
% 1.94/1.42  #Fact    : 0
% 1.94/1.42  #Define  : 0
% 1.94/1.42  #Split   : 0
% 1.94/1.42  #Chain   : 0
% 1.94/1.42  #Close   : 0
% 1.94/1.42  
% 1.94/1.42  Ordering : KBO
% 1.94/1.42  
% 1.94/1.42  Simplification rules
% 1.94/1.42  ----------------------
% 1.94/1.42  #Subsume      : 0
% 1.94/1.42  #Demod        : 4
% 1.94/1.42  #Tautology    : 5
% 1.94/1.42  #SimpNegUnit  : 1
% 1.94/1.42  #BackRed      : 0
% 1.94/1.42  
% 1.94/1.42  #Partial instantiations: 0
% 1.94/1.42  #Strategies tried      : 1
% 1.94/1.42  
% 1.94/1.42  Timing (in seconds)
% 1.94/1.42  ----------------------
% 1.94/1.42  Preprocessing        : 0.44
% 1.94/1.42  Parsing              : 0.23
% 1.94/1.42  CNF conversion       : 0.03
% 1.94/1.42  Main loop            : 0.15
% 1.94/1.42  Inferencing          : 0.06
% 1.94/1.42  Reduction            : 0.04
% 1.94/1.42  Demodulation         : 0.03
% 1.94/1.42  BG Simplification    : 0.02
% 1.94/1.42  Subsumption          : 0.03
% 1.94/1.42  Abstraction          : 0.01
% 1.94/1.42  MUC search           : 0.00
% 1.94/1.42  Cooper               : 0.00
% 1.94/1.42  Total                : 0.63
% 1.94/1.42  Index Insertion      : 0.00
% 1.94/1.42  Index Deletion       : 0.00
% 1.94/1.42  Index Matching       : 0.00
% 1.94/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
