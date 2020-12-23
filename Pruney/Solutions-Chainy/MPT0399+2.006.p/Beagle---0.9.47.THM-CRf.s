%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:32 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  51 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_4'(A_52,B_53,C_54),B_53)
      | ~ r2_hidden(C_54,A_52)
      | ~ r1_setfam_1(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [B_55,C_56,A_57] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_hidden(C_56,A_57)
      | ~ r1_setfam_1(A_57,B_55) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_139,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | ~ r1_setfam_1(A_59,B_58)
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_153,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_41,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_2'(A_33,B_34),A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_36,B_37] :
      ( ~ v1_xboole_0(A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_153,c_63])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.87/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.87/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.17  
% 1.87/1.18  tff(f_60, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.87/1.18  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.87/1.18  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.87/1.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.18  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.87/1.18  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.18  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.18  tff(c_26, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_115, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_4'(A_52, B_53, C_54), B_53) | ~r2_hidden(C_54, A_52) | ~r1_setfam_1(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_123, plain, (![B_55, C_56, A_57]: (~v1_xboole_0(B_55) | ~r2_hidden(C_56, A_57) | ~r1_setfam_1(A_57, B_55))), inference(resolution, [status(thm)], [c_115, c_2])).
% 1.87/1.18  tff(c_139, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | ~r1_setfam_1(A_59, B_58) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_4, c_123])).
% 1.87/1.18  tff(c_148, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_139])).
% 1.87/1.18  tff(c_153, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_148])).
% 1.87/1.18  tff(c_41, plain, (![A_33, B_34]: (r2_hidden('#skF_2'(A_33, B_34), A_33) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.18  tff(c_58, plain, (![A_36, B_37]: (~v1_xboole_0(A_36) | r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.87/1.18  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.18  tff(c_63, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_58, c_14])).
% 1.87/1.18  tff(c_156, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_153, c_63])).
% 1.87/1.18  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_156])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 28
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 1
% 1.87/1.18  #Tautology    : 7
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.19  Preprocessing        : 0.28
% 1.87/1.19  Parsing              : 0.15
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.15
% 1.87/1.19  Inferencing          : 0.06
% 1.87/1.19  Reduction            : 0.04
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.03
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.45
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
