%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:15 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  59 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C,D] :
            ( ( r2_hidden(C,A)
              & r2_hidden(D,B) )
           => r1_xboole_0(C,D) )
       => r1_xboole_0(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_8,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [C_16,D_17] :
      ( r1_xboole_0(C_16,D_17)
      | ~ r2_hidden(D_17,'#skF_3')
      | ~ r2_hidden(C_16,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    ! [C_18,B_19] :
      ( r1_xboole_0(C_18,'#skF_1'('#skF_3',B_19))
      | ~ r2_hidden(C_18,'#skF_2')
      | r1_xboole_0(k3_tarski('#skF_3'),B_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_20,C_21] :
      ( r1_xboole_0('#skF_1'('#skF_3',B_20),C_21)
      | ~ r2_hidden(C_21,'#skF_2')
      | r1_xboole_0(k3_tarski('#skF_3'),B_20) ) ),
    inference(resolution,[status(thm)],[c_19,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( ~ r1_xboole_0('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41,plain,(
    ! [C_22] :
      ( ~ r2_hidden(C_22,'#skF_2')
      | r1_xboole_0(k3_tarski('#skF_3'),C_22) ) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_45,plain,(
    ! [C_23] :
      ( r1_xboole_0(C_23,k3_tarski('#skF_3'))
      | ~ r2_hidden(C_23,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_57,plain,(
    ! [A_24] :
      ( r1_xboole_0(k3_tarski(A_24),k3_tarski('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_24,k3_tarski('#skF_3')),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_61,plain,(
    r1_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_8,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  %$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.12  
% 1.61/1.13  tff(f_46, negated_conjecture, ~(![A, B]: ((![C, D]: ((r2_hidden(C, A) & r2_hidden(D, B)) => r1_xboole_0(C, D))) => r1_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_zfmisc_1)).
% 1.61/1.13  tff(f_36, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 1.61/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.61/1.13  tff(c_8, plain, (~r1_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.13  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.13  tff(c_14, plain, (![C_16, D_17]: (r1_xboole_0(C_16, D_17) | ~r2_hidden(D_17, '#skF_3') | ~r2_hidden(C_16, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.13  tff(c_19, plain, (![C_18, B_19]: (r1_xboole_0(C_18, '#skF_1'('#skF_3', B_19)) | ~r2_hidden(C_18, '#skF_2') | r1_xboole_0(k3_tarski('#skF_3'), B_19))), inference(resolution, [status(thm)], [c_6, c_14])).
% 1.61/1.13  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.13  tff(c_30, plain, (![B_20, C_21]: (r1_xboole_0('#skF_1'('#skF_3', B_20), C_21) | ~r2_hidden(C_21, '#skF_2') | r1_xboole_0(k3_tarski('#skF_3'), B_20))), inference(resolution, [status(thm)], [c_19, c_2])).
% 1.61/1.13  tff(c_4, plain, (![A_3, B_4]: (~r1_xboole_0('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.13  tff(c_41, plain, (![C_22]: (~r2_hidden(C_22, '#skF_2') | r1_xboole_0(k3_tarski('#skF_3'), C_22))), inference(resolution, [status(thm)], [c_30, c_4])).
% 1.61/1.13  tff(c_45, plain, (![C_23]: (r1_xboole_0(C_23, k3_tarski('#skF_3')) | ~r2_hidden(C_23, '#skF_2'))), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.61/1.13  tff(c_57, plain, (![A_24]: (r1_xboole_0(k3_tarski(A_24), k3_tarski('#skF_3')) | ~r2_hidden('#skF_1'(A_24, k3_tarski('#skF_3')), '#skF_2'))), inference(resolution, [status(thm)], [c_45, c_4])).
% 1.61/1.13  tff(c_61, plain, (r1_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.61/1.13  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_8, c_61])).
% 1.61/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  Inference rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Ref     : 0
% 1.61/1.13  #Sup     : 12
% 1.61/1.13  #Fact    : 0
% 1.61/1.13  #Define  : 0
% 1.61/1.13  #Split   : 0
% 1.61/1.13  #Chain   : 0
% 1.61/1.13  #Close   : 0
% 1.61/1.13  
% 1.61/1.13  Ordering : KBO
% 1.61/1.13  
% 1.61/1.13  Simplification rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Subsume      : 2
% 1.61/1.13  #Demod        : 0
% 1.61/1.13  #Tautology    : 0
% 1.61/1.13  #SimpNegUnit  : 1
% 1.61/1.13  #BackRed      : 0
% 1.61/1.13  
% 1.61/1.13  #Partial instantiations: 0
% 1.61/1.13  #Strategies tried      : 1
% 1.61/1.13  
% 1.61/1.13  Timing (in seconds)
% 1.61/1.13  ----------------------
% 1.61/1.13  Preprocessing        : 0.25
% 1.61/1.13  Parsing              : 0.14
% 1.61/1.13  CNF conversion       : 0.02
% 1.61/1.13  Main loop            : 0.11
% 1.61/1.13  Inferencing          : 0.06
% 1.61/1.13  Reduction            : 0.01
% 1.61/1.13  Demodulation         : 0.00
% 1.61/1.13  BG Simplification    : 0.01
% 1.61/1.13  Subsumption          : 0.03
% 1.61/1.13  Abstraction          : 0.00
% 1.61/1.13  MUC search           : 0.00
% 1.61/1.13  Cooper               : 0.00
% 1.61/1.13  Total                : 0.38
% 1.61/1.13  Index Insertion      : 0.00
% 1.61/1.13  Index Deletion       : 0.00
% 1.61/1.13  Index Matching       : 0.00
% 1.61/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
