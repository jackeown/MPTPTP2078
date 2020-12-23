%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  78 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_107,plain,(
    ! [A_13,B_32] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_13),B_32),A_13)
      | r1_tarski(k1_zfmisc_1(A_13),B_32) ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [A_33] : r1_tarski(A_33,A_33) ),
    inference(resolution,[status(thm)],[c_97,c_6])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_112,plain,(
    ! [A_33] : k3_xboole_0(A_33,A_33) = A_33 ),
    inference(resolution,[status(thm)],[c_108,c_12])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(k3_xboole_0(A_28,C_29),B_30)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_54,C_55,B_56] :
      ( k3_xboole_0(k3_xboole_0(A_54,C_55),B_56) = k3_xboole_0(A_54,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(resolution,[status(thm)],[c_83,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_1,B_2,B_30] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_30)
      | ~ r1_tarski(B_2,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_608,plain,(
    ! [A_74,C_75,B_76,B_77] :
      ( r1_tarski(k3_xboole_0(A_74,C_75),B_76)
      | ~ r1_tarski(B_77,B_76)
      | ~ r1_tarski(A_74,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_95])).

tff(c_627,plain,(
    ! [A_78,C_79] :
      ( r1_tarski(k3_xboole_0(A_78,C_79),'#skF_5')
      | ~ r1_tarski(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_608])).

tff(c_670,plain,(
    ! [A_80] :
      ( r1_tarski(A_80,'#skF_5')
      | ~ r1_tarski(A_80,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_627])).

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

tff(c_82,plain,(
    ! [A_26,A_13] :
      ( r1_tarski(A_26,k1_zfmisc_1(A_13))
      | ~ r1_tarski('#skF_1'(A_26,k1_zfmisc_1(A_13)),A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_843,plain,(
    ! [A_90] :
      ( r1_tarski(A_90,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_90,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_670,c_82])).

tff(c_847,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_107,c_843])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.77/1.40  
% 2.77/1.40  %Foreground sorts:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Background operators:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Foreground operators:
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.40  
% 2.77/1.41  tff(f_54, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.77/1.41  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.41  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.77/1.41  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.77/1.41  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.77/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.77/1.41  tff(c_26, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.41  tff(c_97, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.41  tff(c_14, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.41  tff(c_107, plain, (![A_13, B_32]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_13), B_32), A_13) | r1_tarski(k1_zfmisc_1(A_13), B_32))), inference(resolution, [status(thm)], [c_97, c_14])).
% 2.77/1.41  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.41  tff(c_108, plain, (![A_33]: (r1_tarski(A_33, A_33))), inference(resolution, [status(thm)], [c_97, c_6])).
% 2.77/1.41  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.41  tff(c_112, plain, (![A_33]: (k3_xboole_0(A_33, A_33)=A_33)), inference(resolution, [status(thm)], [c_108, c_12])).
% 2.77/1.41  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.41  tff(c_83, plain, (![A_28, C_29, B_30]: (r1_tarski(k3_xboole_0(A_28, C_29), B_30) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.41  tff(c_197, plain, (![A_54, C_55, B_56]: (k3_xboole_0(k3_xboole_0(A_54, C_55), B_56)=k3_xboole_0(A_54, C_55) | ~r1_tarski(A_54, B_56))), inference(resolution, [status(thm)], [c_83, c_12])).
% 2.77/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.41  tff(c_95, plain, (![A_1, B_2, B_30]: (r1_tarski(k3_xboole_0(A_1, B_2), B_30) | ~r1_tarski(B_2, B_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.77/1.41  tff(c_608, plain, (![A_74, C_75, B_76, B_77]: (r1_tarski(k3_xboole_0(A_74, C_75), B_76) | ~r1_tarski(B_77, B_76) | ~r1_tarski(A_74, B_77))), inference(superposition, [status(thm), theory('equality')], [c_197, c_95])).
% 2.77/1.41  tff(c_627, plain, (![A_78, C_79]: (r1_tarski(k3_xboole_0(A_78, C_79), '#skF_5') | ~r1_tarski(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_608])).
% 2.77/1.41  tff(c_670, plain, (![A_80]: (r1_tarski(A_80, '#skF_5') | ~r1_tarski(A_80, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_627])).
% 2.77/1.41  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.41  tff(c_77, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.41  tff(c_82, plain, (![A_26, A_13]: (r1_tarski(A_26, k1_zfmisc_1(A_13)) | ~r1_tarski('#skF_1'(A_26, k1_zfmisc_1(A_13)), A_13))), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.77/1.41  tff(c_843, plain, (![A_90]: (r1_tarski(A_90, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_90, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_670, c_82])).
% 2.77/1.41  tff(c_847, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_107, c_843])).
% 2.77/1.41  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_847])).
% 2.77/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  Inference rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Ref     : 0
% 2.77/1.41  #Sup     : 208
% 2.77/1.41  #Fact    : 0
% 2.77/1.41  #Define  : 0
% 2.77/1.41  #Split   : 1
% 2.77/1.41  #Chain   : 0
% 2.77/1.41  #Close   : 0
% 2.77/1.41  
% 2.77/1.41  Ordering : KBO
% 2.77/1.41  
% 2.77/1.41  Simplification rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Subsume      : 37
% 2.77/1.41  #Demod        : 44
% 2.77/1.41  #Tautology    : 57
% 2.77/1.41  #SimpNegUnit  : 1
% 2.77/1.41  #BackRed      : 0
% 2.77/1.41  
% 2.77/1.41  #Partial instantiations: 0
% 2.77/1.41  #Strategies tried      : 1
% 2.77/1.41  
% 2.77/1.41  Timing (in seconds)
% 2.77/1.41  ----------------------
% 2.77/1.41  Preprocessing        : 0.26
% 2.77/1.41  Parsing              : 0.13
% 2.77/1.41  CNF conversion       : 0.02
% 2.77/1.41  Main loop            : 0.36
% 2.77/1.41  Inferencing          : 0.13
% 2.77/1.41  Reduction            : 0.11
% 2.77/1.41  Demodulation         : 0.09
% 2.77/1.41  BG Simplification    : 0.02
% 2.77/1.41  Subsumption          : 0.08
% 2.77/1.41  Abstraction          : 0.02
% 2.77/1.41  MUC search           : 0.00
% 2.77/1.41  Cooper               : 0.00
% 2.77/1.41  Total                : 0.65
% 2.77/1.41  Index Insertion      : 0.00
% 2.77/1.41  Index Deletion       : 0.00
% 2.77/1.41  Index Matching       : 0.00
% 2.77/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
