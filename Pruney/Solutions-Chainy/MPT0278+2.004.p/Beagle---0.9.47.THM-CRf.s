%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_13,B_32] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_13),B_32),A_13)
      | r1_tarski(k1_zfmisc_1(A_13),B_32) ) ),
    inference(resolution,[status(thm)],[c_93,c_14])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_tarski(A_28,k3_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_774,plain,(
    ! [A_75,A_76,B_77] :
      ( r1_tarski(A_75,A_76)
      | ~ r1_tarski(A_75,k3_xboole_0(B_77,A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_821,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_5')
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_774])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2860,plain,(
    ! [A_107,A_108] :
      ( r1_tarski(A_107,k1_zfmisc_1(A_108))
      | ~ r1_tarski('#skF_1'(A_107,k1_zfmisc_1(A_108)),A_108) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_3135,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_114,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_821,c_2860])).

tff(c_3139,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_103,c_3135])).

tff(c_3143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_3139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.68  
% 3.69/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.68  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.69/1.68  
% 3.69/1.68  %Foreground sorts:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Background operators:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Foreground operators:
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.69/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.68  
% 3.69/1.69  tff(f_54, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.69/1.69  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.69/1.69  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.69/1.69  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.69/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.69/1.69  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.69/1.69  tff(c_26, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.69/1.69  tff(c_93, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.69  tff(c_14, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.69/1.69  tff(c_103, plain, (![A_13, B_32]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_13), B_32), A_13) | r1_tarski(k1_zfmisc_1(A_13), B_32))), inference(resolution, [status(thm)], [c_93, c_14])).
% 3.69/1.69  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.69/1.69  tff(c_63, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.69/1.69  tff(c_67, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_63])).
% 3.69/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.69/1.69  tff(c_83, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_tarski(A_28, k3_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.69/1.69  tff(c_774, plain, (![A_75, A_76, B_77]: (r1_tarski(A_75, A_76) | ~r1_tarski(A_75, k3_xboole_0(B_77, A_76)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 3.69/1.69  tff(c_821, plain, (![A_75]: (r1_tarski(A_75, '#skF_5') | ~r1_tarski(A_75, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_774])).
% 3.69/1.69  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.69/1.69  tff(c_77, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.69  tff(c_2860, plain, (![A_107, A_108]: (r1_tarski(A_107, k1_zfmisc_1(A_108)) | ~r1_tarski('#skF_1'(A_107, k1_zfmisc_1(A_108)), A_108))), inference(resolution, [status(thm)], [c_16, c_77])).
% 3.69/1.69  tff(c_3135, plain, (![A_114]: (r1_tarski(A_114, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_114, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_821, c_2860])).
% 3.69/1.69  tff(c_3139, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_103, c_3135])).
% 3.69/1.69  tff(c_3143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_3139])).
% 3.69/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.69  
% 3.69/1.69  Inference rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Ref     : 0
% 3.69/1.69  #Sup     : 736
% 3.69/1.69  #Fact    : 0
% 3.69/1.69  #Define  : 0
% 3.69/1.69  #Split   : 1
% 3.69/1.69  #Chain   : 0
% 3.69/1.69  #Close   : 0
% 3.69/1.69  
% 3.69/1.69  Ordering : KBO
% 3.69/1.69  
% 3.69/1.69  Simplification rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Subsume      : 42
% 3.69/1.69  #Demod        : 734
% 3.69/1.69  #Tautology    : 508
% 3.69/1.69  #SimpNegUnit  : 1
% 3.69/1.69  #BackRed      : 0
% 3.69/1.69  
% 3.69/1.69  #Partial instantiations: 0
% 3.69/1.69  #Strategies tried      : 1
% 3.69/1.69  
% 3.69/1.69  Timing (in seconds)
% 3.69/1.69  ----------------------
% 3.96/1.69  Preprocessing        : 0.28
% 3.96/1.69  Parsing              : 0.16
% 3.96/1.69  CNF conversion       : 0.02
% 3.96/1.69  Main loop            : 0.62
% 3.96/1.69  Inferencing          : 0.20
% 3.96/1.69  Reduction            : 0.27
% 3.96/1.69  Demodulation         : 0.23
% 3.96/1.69  BG Simplification    : 0.02
% 3.96/1.69  Subsumption          : 0.09
% 3.96/1.69  Abstraction          : 0.03
% 3.96/1.69  MUC search           : 0.00
% 3.96/1.69  Cooper               : 0.00
% 3.96/1.69  Total                : 0.92
% 3.96/1.69  Index Insertion      : 0.00
% 3.96/1.69  Index Deletion       : 0.00
% 3.96/1.69  Index Matching       : 0.00
% 3.96/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
