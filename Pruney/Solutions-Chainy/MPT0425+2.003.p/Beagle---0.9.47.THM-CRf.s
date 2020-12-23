%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   37 (  64 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 ( 112 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(C,k3_tarski(k2_xboole_0(A,B)))
          & ! [D] :
              ( r2_hidden(D,B)
             => r1_xboole_0(D,C) ) )
       => r1_tarski(C,k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_4',k3_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_xboole_0(k3_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [D_12] :
      ( r1_xboole_0(D_12,'#skF_4')
      | ~ r2_hidden(D_12,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    ! [B_22] :
      ( r1_xboole_0('#skF_1'('#skF_3',B_22),'#skF_4')
      | r1_xboole_0(k3_tarski('#skF_3'),B_22) ) ),
    inference(resolution,[status(thm)],[c_20,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_24] :
      ( r1_xboole_0(B_24,k3_tarski('#skF_3'))
      | r1_xboole_0('#skF_1'('#skF_3',B_24),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( ~ r1_xboole_0('#skF_1'(A_8,B_9),B_9)
      | r1_xboole_0(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,
    ( r1_xboole_0(k3_tarski('#skF_3'),'#skF_4')
    | r1_xboole_0('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_55,plain,(
    r1_xboole_0('#skF_4',k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_16,plain,(
    r1_tarski('#skF_4',k3_tarski(k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k3_tarski(A_6),k3_tarski(B_7)) = k3_tarski(k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_xboole_0(A_26,C_28)
      | ~ r1_tarski(A_26,k2_xboole_0(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_31,A_32,B_33] :
      ( r1_tarski(A_31,k3_tarski(A_32))
      | ~ r1_xboole_0(A_31,k3_tarski(B_33))
      | ~ r1_tarski(A_31,k3_tarski(k2_xboole_0(A_32,B_33))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_92,plain,
    ( r1_tarski('#skF_4',k3_tarski('#skF_2'))
    | ~ r1_xboole_0('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_95,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_92])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_95])).

tff(c_99,plain,(
    ~ r1_xboole_0('#skF_4',k3_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_98,plain,(
    r1_xboole_0(k3_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_113,plain,(
    r1_xboole_0('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.69/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.69/1.16  
% 1.69/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(C, k3_tarski(k2_xboole_0(A, B))) & (![D]: (r2_hidden(D, B) => r1_xboole_0(D, C)))) => r1_tarski(C, k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_setfam_1)).
% 1.69/1.17  tff(f_44, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 1.69/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.69/1.17  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 1.69/1.17  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 1.69/1.17  tff(c_12, plain, (~r1_tarski('#skF_4', k3_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.17  tff(c_20, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_xboole_0(k3_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.17  tff(c_14, plain, (![D_12]: (r1_xboole_0(D_12, '#skF_4') | ~r2_hidden(D_12, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.17  tff(c_35, plain, (![B_22]: (r1_xboole_0('#skF_1'('#skF_3', B_22), '#skF_4') | r1_xboole_0(k3_tarski('#skF_3'), B_22))), inference(resolution, [status(thm)], [c_20, c_14])).
% 1.69/1.17  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.17  tff(c_47, plain, (![B_24]: (r1_xboole_0(B_24, k3_tarski('#skF_3')) | r1_xboole_0('#skF_1'('#skF_3', B_24), '#skF_4'))), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.69/1.17  tff(c_8, plain, (![A_8, B_9]: (~r1_xboole_0('#skF_1'(A_8, B_9), B_9) | r1_xboole_0(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.17  tff(c_53, plain, (r1_xboole_0(k3_tarski('#skF_3'), '#skF_4') | r1_xboole_0('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_47, c_8])).
% 1.69/1.17  tff(c_55, plain, (r1_xboole_0('#skF_4', k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_53])).
% 1.69/1.17  tff(c_16, plain, (r1_tarski('#skF_4', k3_tarski(k2_xboole_0('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.17  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k3_tarski(A_6), k3_tarski(B_7))=k3_tarski(k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.17  tff(c_74, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, B_27) | ~r1_xboole_0(A_26, C_28) | ~r1_tarski(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.17  tff(c_86, plain, (![A_31, A_32, B_33]: (r1_tarski(A_31, k3_tarski(A_32)) | ~r1_xboole_0(A_31, k3_tarski(B_33)) | ~r1_tarski(A_31, k3_tarski(k2_xboole_0(A_32, B_33))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 1.69/1.17  tff(c_92, plain, (r1_tarski('#skF_4', k3_tarski('#skF_2')) | ~r1_xboole_0('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_86])).
% 1.69/1.17  tff(c_95, plain, (r1_tarski('#skF_4', k3_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_92])).
% 1.69/1.17  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_95])).
% 1.69/1.17  tff(c_99, plain, (~r1_xboole_0('#skF_4', k3_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_53])).
% 1.69/1.17  tff(c_98, plain, (r1_xboole_0(k3_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 1.69/1.17  tff(c_113, plain, (r1_xboole_0('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_2])).
% 1.69/1.17  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_113])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 23
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 1
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 6
% 1.69/1.17  #Demod        : 2
% 1.69/1.17  #Tautology    : 3
% 1.69/1.17  #SimpNegUnit  : 2
% 1.69/1.17  #BackRed      : 0
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.69/1.17  Preprocessing        : 0.26
% 1.69/1.17  Parsing              : 0.14
% 1.69/1.17  CNF conversion       : 0.02
% 1.69/1.17  Main loop            : 0.16
% 1.69/1.17  Inferencing          : 0.07
% 1.69/1.17  Reduction            : 0.04
% 1.69/1.17  Demodulation         : 0.03
% 1.69/1.17  BG Simplification    : 0.01
% 1.69/1.17  Subsumption          : 0.03
% 1.69/1.17  Abstraction          : 0.01
% 1.69/1.17  MUC search           : 0.00
% 1.69/1.17  Cooper               : 0.00
% 1.69/1.17  Total                : 0.44
% 1.69/1.17  Index Insertion      : 0.00
% 1.69/1.17  Index Deletion       : 0.00
% 1.69/1.17  Index Matching       : 0.00
% 1.69/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
