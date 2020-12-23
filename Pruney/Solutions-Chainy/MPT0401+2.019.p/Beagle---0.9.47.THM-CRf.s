%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  48 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_setfam_1(A,B)
        & r1_setfam_1(B,C) )
     => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_32,B_33] :
      ( r1_setfam_1(A_32,B_33)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( r1_setfam_1(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_52,c_22])).

tff(c_32,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_setfam_1(A_62,C_63)
      | ~ r1_setfam_1(B_64,C_63)
      | ~ r1_setfam_1(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ! [A_62] :
      ( r1_setfam_1(A_62,k1_tarski('#skF_1'))
      | ~ r1_setfam_1(A_62,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_16,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k3_tarski(A_50),k3_tarski(B_51))
      | ~ r1_setfam_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    ! [A_58,A_59] :
      ( r1_tarski(k3_tarski(A_58),A_59)
      | ~ r1_setfam_1(A_58,k1_tarski(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_71])).

tff(c_241,plain,(
    ! [A_84,A_85] :
      ( r1_tarski(A_84,A_85)
      | ~ r1_setfam_1(k1_tarski(A_84),k1_tarski(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_103])).

tff(c_252,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,'#skF_1')
      | ~ r1_setfam_1(k1_tarski(A_86),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_125,c_241])).

tff(c_258,plain,(
    ! [A_87] :
      ( r1_tarski(A_87,'#skF_1')
      | ~ r2_hidden(A_87,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_252])).

tff(c_261,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_258])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.21/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.35  
% 2.26/1.36  tff(f_67, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.26/1.36  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.26/1.36  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.26/1.36  tff(f_59, axiom, (![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_setfam_1)).
% 2.26/1.36  tff(f_41, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.26/1.36  tff(f_53, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.26/1.36  tff(c_28, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.36  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.36  tff(c_52, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.36  tff(c_22, plain, (![A_32, B_33]: (r1_setfam_1(A_32, B_33) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.36  tff(c_56, plain, (![A_44, B_45]: (r1_setfam_1(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_52, c_22])).
% 2.26/1.36  tff(c_32, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.36  tff(c_116, plain, (![A_62, C_63, B_64]: (r1_setfam_1(A_62, C_63) | ~r1_setfam_1(B_64, C_63) | ~r1_setfam_1(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.36  tff(c_125, plain, (![A_62]: (r1_setfam_1(A_62, k1_tarski('#skF_1')) | ~r1_setfam_1(A_62, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_116])).
% 2.26/1.36  tff(c_16, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.36  tff(c_71, plain, (![A_50, B_51]: (r1_tarski(k3_tarski(A_50), k3_tarski(B_51)) | ~r1_setfam_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.36  tff(c_103, plain, (![A_58, A_59]: (r1_tarski(k3_tarski(A_58), A_59) | ~r1_setfam_1(A_58, k1_tarski(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_71])).
% 2.26/1.36  tff(c_241, plain, (![A_84, A_85]: (r1_tarski(A_84, A_85) | ~r1_setfam_1(k1_tarski(A_84), k1_tarski(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_103])).
% 2.26/1.36  tff(c_252, plain, (![A_86]: (r1_tarski(A_86, '#skF_1') | ~r1_setfam_1(k1_tarski(A_86), '#skF_2'))), inference(resolution, [status(thm)], [c_125, c_241])).
% 2.26/1.36  tff(c_258, plain, (![A_87]: (r1_tarski(A_87, '#skF_1') | ~r2_hidden(A_87, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_252])).
% 2.26/1.36  tff(c_261, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_258])).
% 2.26/1.36  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_261])).
% 2.26/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  
% 2.26/1.36  Inference rules
% 2.26/1.36  ----------------------
% 2.26/1.36  #Ref     : 0
% 2.26/1.36  #Sup     : 54
% 2.26/1.36  #Fact    : 0
% 2.26/1.36  #Define  : 0
% 2.26/1.36  #Split   : 1
% 2.26/1.36  #Chain   : 0
% 2.26/1.36  #Close   : 0
% 2.26/1.36  
% 2.26/1.36  Ordering : KBO
% 2.26/1.36  
% 2.26/1.36  Simplification rules
% 2.26/1.36  ----------------------
% 2.26/1.36  #Subsume      : 3
% 2.26/1.36  #Demod        : 2
% 2.26/1.36  #Tautology    : 10
% 2.26/1.36  #SimpNegUnit  : 1
% 2.26/1.36  #BackRed      : 0
% 2.26/1.36  
% 2.26/1.36  #Partial instantiations: 0
% 2.26/1.36  #Strategies tried      : 1
% 2.26/1.36  
% 2.26/1.36  Timing (in seconds)
% 2.26/1.36  ----------------------
% 2.26/1.36  Preprocessing        : 0.31
% 2.26/1.36  Parsing              : 0.17
% 2.26/1.36  CNF conversion       : 0.02
% 2.26/1.36  Main loop            : 0.21
% 2.26/1.36  Inferencing          : 0.08
% 2.26/1.36  Reduction            : 0.05
% 2.26/1.36  Demodulation         : 0.04
% 2.26/1.36  BG Simplification    : 0.01
% 2.26/1.36  Subsumption          : 0.05
% 2.26/1.36  Abstraction          : 0.01
% 2.26/1.36  MUC search           : 0.00
% 2.26/1.36  Cooper               : 0.00
% 2.26/1.36  Total                : 0.54
% 2.26/1.36  Index Insertion      : 0.00
% 2.26/1.36  Index Deletion       : 0.00
% 2.26/1.36  Index Matching       : 0.00
% 2.26/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
