%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  43 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_19,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_23,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_368,plain,(
    ! [C_53,A_54,B_55] :
      ( k2_xboole_0(k9_relat_1(C_53,A_54),k9_relat_1(C_53,B_55)) = k9_relat_1(C_53,k2_xboole_0(A_54,B_55))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_1'(A_23,B_24),B_24)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_25] : r1_tarski(A_25,A_25) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_45,c_8])).

tff(c_402,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k9_relat_1(C_56,A_57),k9_relat_1(C_56,k2_xboole_0(A_57,B_58)))
      | ~ v1_relat_1(C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_59])).

tff(c_423,plain,(
    ! [C_59] :
      ( r1_tarski(k9_relat_1(C_59,'#skF_2'),k9_relat_1(C_59,'#skF_3'))
      | ~ v1_relat_1(C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_402])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_426,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_423,c_14])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.27  
% 2.04/1.27  %Foreground sorts:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Background operators:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Foreground operators:
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.27  
% 2.04/1.28  tff(f_51, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.04/1.28  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.04/1.28  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 2.04/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.28  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.04/1.28  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.28  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.28  tff(c_19, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.28  tff(c_23, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_19])).
% 2.04/1.28  tff(c_368, plain, (![C_53, A_54, B_55]: (k2_xboole_0(k9_relat_1(C_53, A_54), k9_relat_1(C_53, B_55))=k9_relat_1(C_53, k2_xboole_0(A_54, B_55)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.28  tff(c_39, plain, (![A_23, B_24]: (~r2_hidden('#skF_1'(A_23, B_24), B_24) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.28  tff(c_45, plain, (![A_25]: (r1_tarski(A_25, A_25))), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.04/1.28  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.28  tff(c_59, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_45, c_8])).
% 2.04/1.28  tff(c_402, plain, (![C_56, A_57, B_58]: (r1_tarski(k9_relat_1(C_56, A_57), k9_relat_1(C_56, k2_xboole_0(A_57, B_58))) | ~v1_relat_1(C_56))), inference(superposition, [status(thm), theory('equality')], [c_368, c_59])).
% 2.04/1.28  tff(c_423, plain, (![C_59]: (r1_tarski(k9_relat_1(C_59, '#skF_2'), k9_relat_1(C_59, '#skF_3')) | ~v1_relat_1(C_59))), inference(superposition, [status(thm), theory('equality')], [c_23, c_402])).
% 2.04/1.28  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.28  tff(c_426, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_423, c_14])).
% 2.04/1.28  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_426])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 93
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 0
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 4
% 2.04/1.28  #Demod        : 50
% 2.04/1.28  #Tautology    : 54
% 2.04/1.28  #SimpNegUnit  : 0
% 2.04/1.28  #BackRed      : 0
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.27
% 2.04/1.28  Parsing              : 0.15
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.24
% 2.04/1.28  Inferencing          : 0.10
% 2.04/1.28  Reduction            : 0.07
% 2.04/1.28  Demodulation         : 0.06
% 2.04/1.28  BG Simplification    : 0.01
% 2.04/1.28  Subsumption          : 0.04
% 2.04/1.28  Abstraction          : 0.01
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.54
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
