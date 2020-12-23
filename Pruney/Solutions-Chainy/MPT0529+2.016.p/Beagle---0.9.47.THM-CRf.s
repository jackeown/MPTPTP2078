%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  69 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [C_21,B_22,A_23] :
      ( r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_27,B_28,B_29] :
      ( r2_hidden('#skF_1'(A_27,B_28),B_29)
      | ~ r1_tarski(A_27,B_29)
      | r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_34,B_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski(A_34,B_37)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_111,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),'#skF_3')
      | ~ r1_tarski(A_38,'#skF_2')
      | r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_40] :
      ( ~ r1_tarski(A_40,'#skF_2')
      | r1_tarski(A_40,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_132,plain,(
    ! [B_41] :
      ( r1_tarski(k2_relat_1(k8_relat_1('#skF_2',B_41)),'#skF_3')
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_10,c_120])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_158,plain,(
    ! [B_47] :
      ( k8_relat_1('#skF_3',k8_relat_1('#skF_2',B_47)) = k8_relat_1('#skF_2',B_47)
      | ~ v1_relat_1(k8_relat_1('#skF_2',B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_168,plain,(
    ! [B_48] :
      ( k8_relat_1('#skF_3',k8_relat_1('#skF_2',B_48)) = k8_relat_1('#skF_2',B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_14,plain,(
    k8_relat_1('#skF_3',k8_relat_1('#skF_2','#skF_4')) != k8_relat_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_14])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.17  
% 1.91/1.18  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.91/1.18  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.91/1.18  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 1.91/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.18  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.91/1.18  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.18  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.18  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.18  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_29, plain, (![C_21, B_22, A_23]: (r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_59, plain, (![A_27, B_28, B_29]: (r2_hidden('#skF_1'(A_27, B_28), B_29) | ~r1_tarski(A_27, B_29) | r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_6, c_29])).
% 1.91/1.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_101, plain, (![A_34, B_35, B_36, B_37]: (r2_hidden('#skF_1'(A_34, B_35), B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski(A_34, B_37) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.91/1.18  tff(c_111, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), '#skF_3') | ~r1_tarski(A_38, '#skF_2') | r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_16, c_101])).
% 1.91/1.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_120, plain, (![A_40]: (~r1_tarski(A_40, '#skF_2') | r1_tarski(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_111, c_4])).
% 1.91/1.18  tff(c_132, plain, (![B_41]: (r1_tarski(k2_relat_1(k8_relat_1('#skF_2', B_41)), '#skF_3') | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_10, c_120])).
% 1.91/1.18  tff(c_12, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.18  tff(c_158, plain, (![B_47]: (k8_relat_1('#skF_3', k8_relat_1('#skF_2', B_47))=k8_relat_1('#skF_2', B_47) | ~v1_relat_1(k8_relat_1('#skF_2', B_47)) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_132, c_12])).
% 1.91/1.18  tff(c_168, plain, (![B_48]: (k8_relat_1('#skF_3', k8_relat_1('#skF_2', B_48))=k8_relat_1('#skF_2', B_48) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_8, c_158])).
% 1.91/1.18  tff(c_14, plain, (k8_relat_1('#skF_3', k8_relat_1('#skF_2', '#skF_4'))!=k8_relat_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.18  tff(c_177, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_14])).
% 1.91/1.18  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_177])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 0
% 1.91/1.18  #Sup     : 41
% 1.91/1.18  #Fact    : 0
% 1.91/1.18  #Define  : 0
% 1.91/1.18  #Split   : 0
% 1.91/1.18  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 7
% 1.91/1.18  #Demod        : 3
% 1.91/1.18  #Tautology    : 13
% 1.91/1.18  #SimpNegUnit  : 0
% 1.91/1.18  #BackRed      : 0
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.18  ----------------------
% 1.91/1.18  Preprocessing        : 0.25
% 1.91/1.18  Parsing              : 0.14
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.17
% 1.91/1.18  Inferencing          : 0.08
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.04
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.44
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
