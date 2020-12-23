%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_18,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_1'(A_12,B_13),A_12)
      | r1_tarski(k3_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(k1_tarski(A_44),B_45) = k1_tarski(A_44)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_83,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(k3_xboole_0(A_25,C_26),B_27)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_2,A_1,B_27] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_27)
      | ~ r1_tarski(A_1,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_340,plain,(
    ! [A_50,B_51,B_52] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r1_tarski(B_52,B_51)
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_118])).

tff(c_359,plain,(
    ! [A_53] :
      ( r1_tarski(k1_tarski(A_53),'#skF_3')
      | ~ r2_hidden(A_53,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_340])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_390,plain,(
    ! [A_57] :
      ( r2_hidden(A_57,'#skF_3')
      | ~ r2_hidden(A_57,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_359,c_8])).

tff(c_467,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_1'('#skF_2',B_63),'#skF_3')
      | r1_tarski(k3_tarski('#skF_2'),B_63) ) ),
    inference(resolution,[status(thm)],[c_16,c_390])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_243,plain,(
    ! [A_42,B_43] :
      ( ~ r1_tarski('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(k3_tarski(A_42),B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [A_42,B_11] :
      ( r1_tarski(k3_tarski(A_42),k3_tarski(B_11))
      | ~ r2_hidden('#skF_1'(A_42,k3_tarski(B_11)),B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_243])).

tff(c_471,plain,(
    r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_467,c_247])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_18,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.15/1.31  
% 2.15/1.31  %Foreground sorts:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Background operators:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Foreground operators:
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.31  
% 2.33/1.32  tff(f_55, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.33/1.32  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.33/1.32  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.33/1.32  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.33/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.33/1.32  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.33/1.32  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.33/1.32  tff(c_18, plain, (~r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.32  tff(c_16, plain, (![A_12, B_13]: (r2_hidden('#skF_1'(A_12, B_13), A_12) | r1_tarski(k3_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.32  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.32  tff(c_83, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.32  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.32  tff(c_248, plain, (![A_44, B_45]: (k3_xboole_0(k1_tarski(A_44), B_45)=k1_tarski(A_44) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_83, c_6])).
% 2.33/1.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.32  tff(c_106, plain, (![A_25, C_26, B_27]: (r1_tarski(k3_xboole_0(A_25, C_26), B_27) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.32  tff(c_118, plain, (![B_2, A_1, B_27]: (r1_tarski(k3_xboole_0(B_2, A_1), B_27) | ~r1_tarski(A_1, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 2.33/1.32  tff(c_340, plain, (![A_50, B_51, B_52]: (r1_tarski(k1_tarski(A_50), B_51) | ~r1_tarski(B_52, B_51) | ~r2_hidden(A_50, B_52))), inference(superposition, [status(thm), theory('equality')], [c_248, c_118])).
% 2.33/1.32  tff(c_359, plain, (![A_53]: (r1_tarski(k1_tarski(A_53), '#skF_3') | ~r2_hidden(A_53, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_340])).
% 2.33/1.32  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.32  tff(c_390, plain, (![A_57]: (r2_hidden(A_57, '#skF_3') | ~r2_hidden(A_57, '#skF_2'))), inference(resolution, [status(thm)], [c_359, c_8])).
% 2.33/1.32  tff(c_467, plain, (![B_63]: (r2_hidden('#skF_1'('#skF_2', B_63), '#skF_3') | r1_tarski(k3_tarski('#skF_2'), B_63))), inference(resolution, [status(thm)], [c_16, c_390])).
% 2.33/1.32  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.33/1.32  tff(c_243, plain, (![A_42, B_43]: (~r1_tarski('#skF_1'(A_42, B_43), B_43) | r1_tarski(k3_tarski(A_42), B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.32  tff(c_247, plain, (![A_42, B_11]: (r1_tarski(k3_tarski(A_42), k3_tarski(B_11)) | ~r2_hidden('#skF_1'(A_42, k3_tarski(B_11)), B_11))), inference(resolution, [status(thm)], [c_12, c_243])).
% 2.33/1.32  tff(c_471, plain, (r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_467, c_247])).
% 2.33/1.32  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_18, c_471])).
% 2.33/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  Inference rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Ref     : 0
% 2.33/1.32  #Sup     : 114
% 2.33/1.32  #Fact    : 0
% 2.33/1.32  #Define  : 0
% 2.33/1.32  #Split   : 0
% 2.33/1.32  #Chain   : 0
% 2.33/1.32  #Close   : 0
% 2.33/1.32  
% 2.33/1.32  Ordering : KBO
% 2.33/1.32  
% 2.33/1.32  Simplification rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Subsume      : 20
% 2.33/1.32  #Demod        : 4
% 2.33/1.32  #Tautology    : 52
% 2.33/1.32  #SimpNegUnit  : 1
% 2.33/1.32  #BackRed      : 0
% 2.33/1.32  
% 2.33/1.32  #Partial instantiations: 0
% 2.33/1.32  #Strategies tried      : 1
% 2.33/1.32  
% 2.33/1.32  Timing (in seconds)
% 2.33/1.32  ----------------------
% 2.33/1.32  Preprocessing        : 0.25
% 2.33/1.32  Parsing              : 0.14
% 2.33/1.32  CNF conversion       : 0.02
% 2.33/1.32  Main loop            : 0.26
% 2.33/1.32  Inferencing          : 0.11
% 2.33/1.32  Reduction            : 0.07
% 2.33/1.32  Demodulation         : 0.05
% 2.33/1.32  BG Simplification    : 0.02
% 2.33/1.32  Subsumption          : 0.05
% 2.33/1.32  Abstraction          : 0.01
% 2.33/1.33  MUC search           : 0.00
% 2.33/1.33  Cooper               : 0.00
% 2.33/1.33  Total                : 0.54
% 2.33/1.33  Index Insertion      : 0.00
% 2.33/1.33  Index Deletion       : 0.00
% 2.33/1.33  Index Matching       : 0.00
% 2.33/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
