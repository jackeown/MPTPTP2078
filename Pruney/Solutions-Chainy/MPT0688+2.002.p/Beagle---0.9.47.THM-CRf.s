%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  72 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(k1_tarski(A_35),B_36) = k1_xboole_0
      | r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [B_53,A_54] :
      ( k10_relat_1(B_53,A_54) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,(
    ! [B_63,B_64] :
      ( k10_relat_1(B_63,B_64) = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | k3_xboole_0(k2_relat_1(B_63),B_64) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_257,plain,(
    ! [B_68,A_69] :
      ( k10_relat_1(B_68,A_69) = k1_xboole_0
      | ~ v1_relat_1(B_68)
      | k3_xboole_0(A_69,k2_relat_1(B_68)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_230])).

tff(c_328,plain,(
    ! [B_72,A_73] :
      ( k10_relat_1(B_72,k1_tarski(A_73)) = k1_xboole_0
      | ~ v1_relat_1(B_72)
      | r2_hidden(A_73,k2_relat_1(B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_257])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_347,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,k2_relat_1(B_84))
      | k10_relat_1(B_84,k1_tarski('#skF_1'(A_83,k2_relat_1(B_84)))) = k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_328,c_6])).

tff(c_30,plain,(
    ! [C_25] :
      ( k10_relat_1('#skF_3',k1_tarski(C_25)) != k1_xboole_0
      | ~ r2_hidden(C_25,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_354,plain,(
    ! [A_83] :
      ( ~ r2_hidden('#skF_1'(A_83,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_83,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_30])).

tff(c_363,plain,(
    ! [A_85] :
      ( ~ r2_hidden('#skF_1'(A_85,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_85,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_354])).

tff(c_371,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_363])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.25  
% 2.30/1.25  %Foreground sorts:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Background operators:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Foreground operators:
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.30/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.25  
% 2.30/1.26  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 2.30/1.26  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.30/1.26  tff(f_51, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.30/1.26  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.30/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.30/1.26  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.30/1.26  tff(c_28, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.26  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.26  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.26  tff(c_90, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.26  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.26  tff(c_94, plain, (![A_35, B_36]: (k3_xboole_0(k1_tarski(A_35), B_36)=k1_xboole_0 | r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_90, c_10])).
% 2.30/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.26  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.26  tff(c_173, plain, (![B_53, A_54]: (k10_relat_1(B_53, A_54)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.26  tff(c_230, plain, (![B_63, B_64]: (k10_relat_1(B_63, B_64)=k1_xboole_0 | ~v1_relat_1(B_63) | k3_xboole_0(k2_relat_1(B_63), B_64)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_173])).
% 2.30/1.26  tff(c_257, plain, (![B_68, A_69]: (k10_relat_1(B_68, A_69)=k1_xboole_0 | ~v1_relat_1(B_68) | k3_xboole_0(A_69, k2_relat_1(B_68))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_230])).
% 2.30/1.26  tff(c_328, plain, (![B_72, A_73]: (k10_relat_1(B_72, k1_tarski(A_73))=k1_xboole_0 | ~v1_relat_1(B_72) | r2_hidden(A_73, k2_relat_1(B_72)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_257])).
% 2.30/1.26  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.26  tff(c_347, plain, (![A_83, B_84]: (r1_tarski(A_83, k2_relat_1(B_84)) | k10_relat_1(B_84, k1_tarski('#skF_1'(A_83, k2_relat_1(B_84))))=k1_xboole_0 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_328, c_6])).
% 2.30/1.26  tff(c_30, plain, (![C_25]: (k10_relat_1('#skF_3', k1_tarski(C_25))!=k1_xboole_0 | ~r2_hidden(C_25, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.26  tff(c_354, plain, (![A_83]: (~r2_hidden('#skF_1'(A_83, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_83, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_347, c_30])).
% 2.30/1.26  tff(c_363, plain, (![A_85]: (~r2_hidden('#skF_1'(A_85, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_85, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_354])).
% 2.30/1.26  tff(c_371, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_363])).
% 2.30/1.26  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_371])).
% 2.30/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.26  
% 2.30/1.26  Inference rules
% 2.30/1.26  ----------------------
% 2.30/1.26  #Ref     : 0
% 2.30/1.26  #Sup     : 76
% 2.30/1.26  #Fact    : 0
% 2.30/1.26  #Define  : 0
% 2.30/1.26  #Split   : 0
% 2.30/1.26  #Chain   : 0
% 2.30/1.26  #Close   : 0
% 2.30/1.26  
% 2.30/1.26  Ordering : KBO
% 2.30/1.26  
% 2.30/1.26  Simplification rules
% 2.30/1.26  ----------------------
% 2.30/1.26  #Subsume      : 21
% 2.30/1.26  #Demod        : 1
% 2.30/1.26  #Tautology    : 39
% 2.30/1.26  #SimpNegUnit  : 1
% 2.30/1.26  #BackRed      : 0
% 2.30/1.26  
% 2.30/1.26  #Partial instantiations: 0
% 2.30/1.26  #Strategies tried      : 1
% 2.30/1.26  
% 2.30/1.26  Timing (in seconds)
% 2.30/1.26  ----------------------
% 2.30/1.27  Preprocessing        : 0.30
% 2.30/1.27  Parsing              : 0.16
% 2.30/1.27  CNF conversion       : 0.02
% 2.30/1.27  Main loop            : 0.21
% 2.30/1.27  Inferencing          : 0.09
% 2.30/1.27  Reduction            : 0.06
% 2.30/1.27  Demodulation         : 0.05
% 2.30/1.27  BG Simplification    : 0.01
% 2.30/1.27  Subsumption          : 0.04
% 2.30/1.27  Abstraction          : 0.01
% 2.30/1.27  MUC search           : 0.00
% 2.30/1.27  Cooper               : 0.00
% 2.30/1.27  Total                : 0.53
% 2.30/1.27  Index Insertion      : 0.00
% 2.30/1.27  Index Deletion       : 0.00
% 2.30/1.27  Index Matching       : 0.00
% 2.30/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
