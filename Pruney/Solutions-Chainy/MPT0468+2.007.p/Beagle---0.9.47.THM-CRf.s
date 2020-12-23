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
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  42 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [A_32,B_33] :
      ( k4_tarski('#skF_3'(A_32,B_33),'#skF_4'(A_32,B_33)) = B_33
      | ~ r2_hidden(B_33,A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [B_23,C_24] : ~ r2_hidden(k4_tarski(B_23,C_24),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_31,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,'#skF_5')
      | ~ r2_hidden(B_34,A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_12])).

tff(c_34,plain,(
    ! [A_35] :
      ( ~ r2_hidden('#skF_1'('#skF_5'),A_35)
      | ~ v1_relat_1(A_35)
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_43,plain,(
    ! [A_36] :
      ( ~ r2_hidden('#skF_1'('#skF_5'),A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_34])).

tff(c_47,plain,
    ( ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.08  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 1.52/1.08  
% 1.52/1.08  %Foreground sorts:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Background operators:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Foreground operators:
% 1.52/1.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.52/1.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.52/1.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.52/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.52/1.08  tff('#skF_5', type, '#skF_5': $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.52/1.08  
% 1.52/1.08  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.52/1.08  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.52/1.08  tff(f_43, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.52/1.08  tff(c_10, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.52/1.08  tff(c_14, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.52/1.08  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.52/1.08  tff(c_19, plain, (![A_32, B_33]: (k4_tarski('#skF_3'(A_32, B_33), '#skF_4'(A_32, B_33))=B_33 | ~r2_hidden(B_33, A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.52/1.08  tff(c_12, plain, (![B_23, C_24]: (~r2_hidden(k4_tarski(B_23, C_24), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.52/1.08  tff(c_31, plain, (![B_34, A_35]: (~r2_hidden(B_34, '#skF_5') | ~r2_hidden(B_34, A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_19, c_12])).
% 1.52/1.08  tff(c_34, plain, (![A_35]: (~r2_hidden('#skF_1'('#skF_5'), A_35) | ~v1_relat_1(A_35) | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_2, c_31])).
% 1.52/1.08  tff(c_43, plain, (![A_36]: (~r2_hidden('#skF_1'('#skF_5'), A_36) | ~v1_relat_1(A_36))), inference(negUnitSimplification, [status(thm)], [c_10, c_34])).
% 1.52/1.08  tff(c_47, plain, (~v1_relat_1('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.52/1.08  tff(c_50, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47])).
% 1.52/1.08  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_50])).
% 1.52/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.08  
% 1.52/1.08  Inference rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Ref     : 0
% 1.52/1.08  #Sup     : 7
% 1.52/1.08  #Fact    : 0
% 1.52/1.08  #Define  : 0
% 1.52/1.08  #Split   : 0
% 1.52/1.08  #Chain   : 0
% 1.52/1.08  #Close   : 0
% 1.52/1.08  
% 1.52/1.08  Ordering : KBO
% 1.52/1.08  
% 1.52/1.08  Simplification rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Subsume      : 0
% 1.52/1.08  #Demod        : 2
% 1.52/1.08  #Tautology    : 3
% 1.52/1.08  #SimpNegUnit  : 2
% 1.52/1.08  #BackRed      : 0
% 1.52/1.08  
% 1.52/1.08  #Partial instantiations: 0
% 1.52/1.08  #Strategies tried      : 1
% 1.52/1.08  
% 1.52/1.08  Timing (in seconds)
% 1.52/1.08  ----------------------
% 1.52/1.09  Preprocessing        : 0.26
% 1.52/1.09  Parsing              : 0.14
% 1.52/1.09  CNF conversion       : 0.02
% 1.52/1.09  Main loop            : 0.08
% 1.52/1.09  Inferencing          : 0.04
% 1.52/1.09  Reduction            : 0.02
% 1.52/1.09  Demodulation         : 0.01
% 1.52/1.09  BG Simplification    : 0.01
% 1.52/1.09  Subsumption          : 0.01
% 1.52/1.09  Abstraction          : 0.00
% 1.52/1.09  MUC search           : 0.00
% 1.52/1.09  Cooper               : 0.00
% 1.52/1.09  Total                : 0.35
% 1.52/1.09  Index Insertion      : 0.00
% 1.52/1.09  Index Deletion       : 0.00
% 1.52/1.09  Index Matching       : 0.00
% 1.52/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
