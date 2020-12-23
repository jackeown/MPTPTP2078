%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  60 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_setfam_1(A,B)
        & r1_setfam_1(B,C) )
     => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( r1_setfam_1(A_22,B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_36,B_37] :
      ( r1_setfam_1(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_30,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_setfam_1(A_51,C_52)
      | ~ r1_setfam_1(B_53,C_52)
      | ~ r1_setfam_1(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_51] :
      ( r1_setfam_1(A_51,k1_tarski('#skF_1'))
      | ~ r1_setfam_1(A_51,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [A_3] : k3_tarski(k1_tarski(A_3)) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_76,plain,(
    ! [A_3] : k3_tarski(k1_tarski(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_92,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k3_tarski(A_45),k3_tarski(B_46))
      | ~ r1_setfam_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r1_setfam_1(k1_tarski(A_49),B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_92])).

tff(c_285,plain,(
    ! [A_77,A_78] :
      ( r1_tarski(A_77,A_78)
      | ~ r1_setfam_1(k1_tarski(A_77),k1_tarski(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_122])).

tff(c_305,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_1')
      | ~ r1_setfam_1(k1_tarski(A_83),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_147,c_285])).

tff(c_311,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,'#skF_1')
      | ~ r2_hidden(A_84,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_63,c_305])).

tff(c_314,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_311])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.16/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.28  
% 2.16/1.30  tff(f_65, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.16/1.30  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.16/1.30  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.16/1.30  tff(f_57, axiom, (![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_setfam_1)).
% 2.16/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.16/1.30  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.16/1.30  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.16/1.30  tff(f_51, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.16/1.30  tff(c_26, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.30  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.30  tff(c_59, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.30  tff(c_20, plain, (![A_22, B_23]: (r1_setfam_1(A_22, B_23) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.30  tff(c_63, plain, (![A_36, B_37]: (r1_setfam_1(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(resolution, [status(thm)], [c_59, c_20])).
% 2.16/1.30  tff(c_30, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.30  tff(c_138, plain, (![A_51, C_52, B_53]: (r1_setfam_1(A_51, C_52) | ~r1_setfam_1(B_53, C_52) | ~r1_setfam_1(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.30  tff(c_147, plain, (![A_51]: (r1_setfam_1(A_51, k1_tarski('#skF_1')) | ~r1_setfam_1(A_51, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_138])).
% 2.16/1.30  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.30  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.30  tff(c_64, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.30  tff(c_73, plain, (![A_3]: (k3_tarski(k1_tarski(A_3))=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 2.16/1.30  tff(c_76, plain, (![A_3]: (k3_tarski(k1_tarski(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73])).
% 2.16/1.30  tff(c_92, plain, (![A_45, B_46]: (r1_tarski(k3_tarski(A_45), k3_tarski(B_46)) | ~r1_setfam_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.30  tff(c_122, plain, (![A_49, B_50]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r1_setfam_1(k1_tarski(A_49), B_50))), inference(superposition, [status(thm), theory('equality')], [c_76, c_92])).
% 2.16/1.30  tff(c_285, plain, (![A_77, A_78]: (r1_tarski(A_77, A_78) | ~r1_setfam_1(k1_tarski(A_77), k1_tarski(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_122])).
% 2.16/1.30  tff(c_305, plain, (![A_83]: (r1_tarski(A_83, '#skF_1') | ~r1_setfam_1(k1_tarski(A_83), '#skF_2'))), inference(resolution, [status(thm)], [c_147, c_285])).
% 2.16/1.30  tff(c_311, plain, (![A_84]: (r1_tarski(A_84, '#skF_1') | ~r2_hidden(A_84, '#skF_2'))), inference(resolution, [status(thm)], [c_63, c_305])).
% 2.16/1.30  tff(c_314, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_311])).
% 2.16/1.30  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_314])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 69
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 1
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 4
% 2.16/1.30  #Demod        : 3
% 2.16/1.30  #Tautology    : 16
% 2.16/1.30  #SimpNegUnit  : 1
% 2.16/1.30  #BackRed      : 0
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.30  Preprocessing        : 0.30
% 2.16/1.30  Parsing              : 0.16
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.23
% 2.16/1.30  Inferencing          : 0.09
% 2.16/1.30  Reduction            : 0.06
% 2.16/1.30  Demodulation         : 0.04
% 2.16/1.30  BG Simplification    : 0.01
% 2.16/1.30  Subsumption          : 0.05
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.56
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
