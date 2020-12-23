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
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  48 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_setfam_1(A,B)
        & r1_setfam_1(B,C) )
     => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_setfam_1(A_14,B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [A_30,B_31] :
      ( r1_setfam_1(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_56,c_16])).

tff(c_26,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_setfam_1(A_44,C_45)
      | ~ r1_setfam_1(B_46,C_45)
      | ~ r1_setfam_1(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    ! [A_44] :
      ( r1_setfam_1(A_44,k1_tarski('#skF_1'))
      | ~ r1_setfam_1(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_109])).

tff(c_14,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k3_tarski(A_32),k3_tarski(B_33))
      | ~ r1_setfam_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(k3_tarski(A_36),A_37)
      | ~ r1_setfam_1(A_36,k1_tarski(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_126,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,A_49)
      | ~ r1_setfam_1(k1_tarski(A_48),k1_tarski(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_137,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_1')
      | ~ r1_setfam_1(k1_tarski(A_50),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_121,c_126])).

tff(c_160,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,'#skF_1')
      | ~ r2_hidden(A_53,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_137])).

tff(c_163,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  
% 1.82/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.82/1.26  
% 1.82/1.26  %Foreground sorts:
% 1.82/1.26  
% 1.82/1.26  
% 1.82/1.26  %Background operators:
% 1.82/1.26  
% 1.82/1.26  
% 1.82/1.26  %Foreground operators:
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.26  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.82/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.26  
% 1.90/1.27  tff(f_61, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 1.90/1.27  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.90/1.27  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.90/1.27  tff(f_53, axiom, (![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_setfam_1)).
% 1.90/1.27  tff(f_39, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.90/1.27  tff(f_47, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.90/1.27  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.27  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.27  tff(c_56, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.27  tff(c_16, plain, (![A_14, B_15]: (r1_setfam_1(A_14, B_15) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.27  tff(c_64, plain, (![A_30, B_31]: (r1_setfam_1(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_56, c_16])).
% 1.90/1.27  tff(c_26, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.27  tff(c_109, plain, (![A_44, C_45, B_46]: (r1_setfam_1(A_44, C_45) | ~r1_setfam_1(B_46, C_45) | ~r1_setfam_1(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.27  tff(c_121, plain, (![A_44]: (r1_setfam_1(A_44, k1_tarski('#skF_1')) | ~r1_setfam_1(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_109])).
% 1.90/1.27  tff(c_14, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.27  tff(c_65, plain, (![A_32, B_33]: (r1_tarski(k3_tarski(A_32), k3_tarski(B_33)) | ~r1_setfam_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.27  tff(c_77, plain, (![A_36, A_37]: (r1_tarski(k3_tarski(A_36), A_37) | ~r1_setfam_1(A_36, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 1.90/1.27  tff(c_126, plain, (![A_48, A_49]: (r1_tarski(A_48, A_49) | ~r1_setfam_1(k1_tarski(A_48), k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_77])).
% 1.90/1.27  tff(c_137, plain, (![A_50]: (r1_tarski(A_50, '#skF_1') | ~r1_setfam_1(k1_tarski(A_50), '#skF_2'))), inference(resolution, [status(thm)], [c_121, c_126])).
% 1.90/1.27  tff(c_160, plain, (![A_53]: (r1_tarski(A_53, '#skF_1') | ~r2_hidden(A_53, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_137])).
% 1.90/1.27  tff(c_163, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_160])).
% 1.90/1.27  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_163])).
% 1.90/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.27  
% 1.90/1.27  Inference rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Ref     : 0
% 1.90/1.27  #Sup     : 33
% 1.90/1.27  #Fact    : 0
% 1.90/1.27  #Define  : 0
% 1.90/1.27  #Split   : 0
% 1.90/1.27  #Chain   : 0
% 1.90/1.27  #Close   : 0
% 1.90/1.27  
% 1.90/1.27  Ordering : KBO
% 1.90/1.27  
% 1.90/1.27  Simplification rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Subsume      : 1
% 1.90/1.27  #Demod        : 1
% 1.90/1.27  #Tautology    : 8
% 1.90/1.27  #SimpNegUnit  : 1
% 1.90/1.27  #BackRed      : 0
% 1.90/1.27  
% 1.90/1.27  #Partial instantiations: 0
% 1.90/1.27  #Strategies tried      : 1
% 1.90/1.27  
% 1.90/1.27  Timing (in seconds)
% 1.90/1.27  ----------------------
% 1.90/1.27  Preprocessing        : 0.30
% 1.90/1.27  Parsing              : 0.16
% 1.90/1.27  CNF conversion       : 0.02
% 1.90/1.27  Main loop            : 0.14
% 1.90/1.27  Inferencing          : 0.06
% 1.90/1.28  Reduction            : 0.04
% 1.90/1.28  Demodulation         : 0.03
% 1.90/1.28  BG Simplification    : 0.01
% 1.90/1.28  Subsumption          : 0.03
% 1.90/1.28  Abstraction          : 0.01
% 1.90/1.28  MUC search           : 0.00
% 1.90/1.28  Cooper               : 0.00
% 1.90/1.28  Total                : 0.46
% 1.90/1.28  Index Insertion      : 0.00
% 1.90/1.28  Index Deletion       : 0.00
% 1.90/1.28  Index Matching       : 0.00
% 1.90/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
