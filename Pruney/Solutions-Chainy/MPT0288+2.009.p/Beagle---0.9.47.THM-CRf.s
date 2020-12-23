%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_28,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_tarski(k3_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_53,plain,(
    ! [D_21,B_22,A_23] :
      ( r2_hidden(D_21,B_22)
      | ~ r2_hidden(D_21,k3_xboole_0(A_23,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,'#skF_5')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_53])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,k3_tarski(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [A_29,B_30] :
      ( ~ r1_tarski('#skF_3'(A_29,B_30),B_30)
      | r1_tarski(k3_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k3_tarski(A_39),k3_tarski(B_40))
      | ~ r2_hidden('#skF_3'(A_39,k3_tarski(B_40)),B_40) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_175,plain,(
    ! [A_43] :
      ( r1_tarski(k3_tarski(A_43),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_43,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_179,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.75/1.16  
% 1.75/1.16  %Foreground sorts:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Background operators:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Foreground operators:
% 1.75/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.75/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.16  
% 1.85/1.17  tff(f_54, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.85/1.17  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.85/1.17  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.85/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.85/1.17  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.85/1.17  tff(c_28, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_tarski(k3_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.17  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_36, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.17  tff(c_44, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_36])).
% 1.85/1.17  tff(c_53, plain, (![D_21, B_22, A_23]: (r2_hidden(D_21, B_22) | ~r2_hidden(D_21, k3_xboole_0(A_23, B_22)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.17  tff(c_56, plain, (![D_21]: (r2_hidden(D_21, '#skF_5') | ~r2_hidden(D_21, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_53])).
% 1.85/1.17  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, k3_tarski(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.17  tff(c_88, plain, (![A_29, B_30]: (~r1_tarski('#skF_3'(A_29, B_30), B_30) | r1_tarski(k3_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.17  tff(c_122, plain, (![A_39, B_40]: (r1_tarski(k3_tarski(A_39), k3_tarski(B_40)) | ~r2_hidden('#skF_3'(A_39, k3_tarski(B_40)), B_40))), inference(resolution, [status(thm)], [c_22, c_88])).
% 1.85/1.17  tff(c_175, plain, (![A_43]: (r1_tarski(k3_tarski(A_43), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_43, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 1.85/1.17  tff(c_179, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_175])).
% 1.85/1.17  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_179])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 36
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 0
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 0
% 1.85/1.17  #Demod        : 0
% 1.85/1.17  #Tautology    : 17
% 1.85/1.17  #SimpNegUnit  : 1
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.26
% 1.85/1.17  Parsing              : 0.14
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.16
% 1.85/1.17  Inferencing          : 0.07
% 1.85/1.17  Reduction            : 0.04
% 1.85/1.17  Demodulation         : 0.02
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.03
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.44
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
