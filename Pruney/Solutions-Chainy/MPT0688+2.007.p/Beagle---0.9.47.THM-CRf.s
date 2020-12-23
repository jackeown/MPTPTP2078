%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,k2_relat_1(B_20))
      | k10_relat_1(B_20,k1_tarski(A_19)) = k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k2_relat_1(B_27))
      | k10_relat_1(B_27,k1_tarski('#skF_1'(A_26,k2_relat_1(B_27)))) = k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_14,plain,(
    ! [C_9] :
      ( k10_relat_1('#skF_3',k1_tarski(C_9)) != k1_xboole_0
      | ~ r2_hidden(C_9,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [A_26] :
      ( ~ r2_hidden('#skF_1'(A_26,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_26,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_79,plain,(
    ! [A_28] :
      ( ~ r2_hidden('#skF_1'(A_28,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_28,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_70])).

tff(c_87,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_12,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:47:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  %$ r2_hidden > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.60/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.16  
% 1.79/1.17  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 1.79/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.79/1.17  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.79/1.17  tff(c_12, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.17  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.17  tff(c_30, plain, (![A_19, B_20]: (r2_hidden(A_19, k2_relat_1(B_20)) | k10_relat_1(B_20, k1_tarski(A_19))=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.17  tff(c_63, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_relat_1(B_27)) | k10_relat_1(B_27, k1_tarski('#skF_1'(A_26, k2_relat_1(B_27))))=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_30, c_4])).
% 1.79/1.17  tff(c_14, plain, (![C_9]: (k10_relat_1('#skF_3', k1_tarski(C_9))!=k1_xboole_0 | ~r2_hidden(C_9, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.17  tff(c_70, plain, (![A_26]: (~r2_hidden('#skF_1'(A_26, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_26, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_14])).
% 1.79/1.17  tff(c_79, plain, (![A_28]: (~r2_hidden('#skF_1'(A_28, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_28, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_70])).
% 1.79/1.17  tff(c_87, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_79])).
% 1.79/1.17  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_12, c_87])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 14
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 0
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 0
% 1.79/1.17  #Demod        : 1
% 1.79/1.17  #Tautology    : 4
% 1.79/1.17  #SimpNegUnit  : 1
% 1.79/1.17  #BackRed      : 0
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.17  Preprocessing        : 0.26
% 1.79/1.17  Parsing              : 0.15
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.12
% 1.79/1.17  Inferencing          : 0.06
% 1.79/1.17  Reduction            : 0.03
% 1.79/1.17  Demodulation         : 0.02
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.02
% 1.79/1.17  Abstraction          : 0.00
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.41
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
