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
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  57 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(k4_tarski('#skF_1'(A_32,B_33),'#skF_2'(A_32,B_33)),A_32)
      | r1_tarski(A_32,B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [B_24,C_25] : ~ r2_hidden(k4_tarski(B_24,C_25),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    ! [B_33] :
      ( r1_tarski('#skF_3',B_33)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_23,c_14])).

tff(c_30,plain,(
    ! [B_33] : r1_tarski('#skF_3',B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_27])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_19,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_xboole_0 = A_29
      | ~ r1_xboole_0(B_30,C_31)
      | ~ r1_tarski(A_29,C_31)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_35,A_36] :
      ( k1_xboole_0 = A_35
      | ~ r1_tarski(A_35,k1_xboole_0)
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

tff(c_35,plain,(
    ! [A_36] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_36) ) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35])).

tff(c_40,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:20:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.61/1.13  
% 1.61/1.13  %Foreground sorts:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Background operators:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Foreground operators:
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.61/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.14  
% 1.61/1.14  tff(f_54, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.61/1.14  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.61/1.14  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.61/1.14  tff(f_35, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.61/1.14  tff(c_12, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.14  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.14  tff(c_23, plain, (![A_32, B_33]: (r2_hidden(k4_tarski('#skF_1'(A_32, B_33), '#skF_2'(A_32, B_33)), A_32) | r1_tarski(A_32, B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.61/1.14  tff(c_14, plain, (![B_24, C_25]: (~r2_hidden(k4_tarski(B_24, C_25), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.14  tff(c_27, plain, (![B_33]: (r1_tarski('#skF_3', B_33) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_23, c_14])).
% 1.61/1.14  tff(c_30, plain, (![B_33]: (r1_tarski('#skF_3', B_33))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_27])).
% 1.61/1.14  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.14  tff(c_19, plain, (![A_29, B_30, C_31]: (k1_xboole_0=A_29 | ~r1_xboole_0(B_30, C_31) | ~r1_tarski(A_29, C_31) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.14  tff(c_32, plain, (![A_35, A_36]: (k1_xboole_0=A_35 | ~r1_tarski(A_35, k1_xboole_0) | ~r1_tarski(A_35, A_36))), inference(resolution, [status(thm)], [c_2, c_19])).
% 1.61/1.14  tff(c_35, plain, (![A_36]: (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', A_36))), inference(resolution, [status(thm)], [c_30, c_32])).
% 1.61/1.14  tff(c_38, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35])).
% 1.61/1.14  tff(c_40, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_38])).
% 1.61/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  Inference rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Ref     : 0
% 1.61/1.14  #Sup     : 3
% 1.61/1.14  #Fact    : 0
% 1.61/1.14  #Define  : 0
% 1.61/1.14  #Split   : 0
% 1.61/1.14  #Chain   : 0
% 1.61/1.14  #Close   : 0
% 1.61/1.14  
% 1.61/1.14  Ordering : KBO
% 1.61/1.14  
% 1.61/1.14  Simplification rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Subsume      : 0
% 1.61/1.14  #Demod        : 2
% 1.61/1.14  #Tautology    : 0
% 1.61/1.14  #SimpNegUnit  : 1
% 1.61/1.14  #BackRed      : 0
% 1.61/1.14  
% 1.61/1.14  #Partial instantiations: 0
% 1.61/1.14  #Strategies tried      : 1
% 1.61/1.14  
% 1.61/1.14  Timing (in seconds)
% 1.61/1.14  ----------------------
% 1.61/1.15  Preprocessing        : 0.27
% 1.61/1.15  Parsing              : 0.14
% 1.61/1.15  CNF conversion       : 0.02
% 1.61/1.15  Main loop            : 0.07
% 1.61/1.15  Inferencing          : 0.03
% 1.61/1.15  Reduction            : 0.02
% 1.61/1.15  Demodulation         : 0.02
% 1.61/1.15  BG Simplification    : 0.01
% 1.61/1.15  Subsumption          : 0.01
% 1.61/1.15  Abstraction          : 0.00
% 1.61/1.15  MUC search           : 0.00
% 1.61/1.15  Cooper               : 0.00
% 1.61/1.15  Total                : 0.36
% 1.61/1.15  Index Insertion      : 0.00
% 1.61/1.15  Index Deletion       : 0.00
% 1.74/1.15  Index Matching       : 0.00
% 1.74/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
