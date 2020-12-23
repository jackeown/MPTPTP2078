%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  93 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

tff(c_32,plain,(
    ! [A_18] : v1_relat_1(k1_wellord2(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_1'(A_23,B_24),B_24)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_26,plain,(
    ! [A_10] :
      ( k3_relat_1(k1_wellord2(A_10)) = A_10
      | ~ v1_relat_1(k1_wellord2(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_10] : k3_relat_1(k1_wellord2(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_63,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),k3_relat_1(A_29))
      | v1_relat_2(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_29,B_2] :
      ( r2_hidden('#skF_2'(A_29),B_2)
      | ~ r1_tarski(k3_relat_1(A_29),B_2)
      | v1_relat_2(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_28,plain,(
    ! [C_16,D_17,A_10] :
      ( r2_hidden(k4_tarski(C_16,D_17),k1_wellord2(A_10))
      | ~ r1_tarski(C_16,D_17)
      | ~ r2_hidden(D_17,A_10)
      | ~ r2_hidden(C_16,A_10)
      | ~ v1_relat_1(k1_wellord2(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_168,plain,(
    ! [C_54,D_55,A_56] :
      ( r2_hidden(k4_tarski(C_54,D_55),k1_wellord2(A_56))
      | ~ r1_tarski(C_54,D_55)
      | ~ r2_hidden(D_55,A_56)
      | ~ r2_hidden(C_54,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_6),'#skF_2'(A_6)),A_6)
      | v1_relat_2(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_175,plain,(
    ! [A_56] :
      ( v1_relat_2(k1_wellord2(A_56))
      | ~ v1_relat_1(k1_wellord2(A_56))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_56)),'#skF_2'(k1_wellord2(A_56)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_56)),A_56) ) ),
    inference(resolution,[status(thm)],[c_168,c_10])).

tff(c_183,plain,(
    ! [A_57] :
      ( v1_relat_2(k1_wellord2(A_57))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_57)),A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_32,c_175])).

tff(c_187,plain,(
    ! [B_2] :
      ( ~ r1_tarski(k3_relat_1(k1_wellord2(B_2)),B_2)
      | v1_relat_2(k1_wellord2(B_2))
      | ~ v1_relat_1(k1_wellord2(B_2)) ) ),
    inference(resolution,[status(thm)],[c_69,c_183])).

tff(c_197,plain,(
    ! [B_2] : v1_relat_2(k1_wellord2(B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57,c_40,c_187])).

tff(c_34,plain,(
    ~ v1_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  %$ r2_hidden > r1_tarski > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.04/1.24  
% 2.04/1.24  %Foreground sorts:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Background operators:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Foreground operators:
% 2.04/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.24  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.04/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.04/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.24  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.04/1.24  
% 2.04/1.25  tff(f_58, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.04/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.25  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.04/1.25  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 2.04/1.25  tff(f_61, negated_conjecture, ~(![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 2.04/1.25  tff(c_32, plain, (![A_18]: (v1_relat_1(k1_wellord2(A_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.25  tff(c_52, plain, (![A_23, B_24]: (~r2_hidden('#skF_1'(A_23, B_24), B_24) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.25  tff(c_57, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.04/1.25  tff(c_26, plain, (![A_10]: (k3_relat_1(k1_wellord2(A_10))=A_10 | ~v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.25  tff(c_40, plain, (![A_10]: (k3_relat_1(k1_wellord2(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.04/1.25  tff(c_63, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), k3_relat_1(A_29)) | v1_relat_2(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.25  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.25  tff(c_69, plain, (![A_29, B_2]: (r2_hidden('#skF_2'(A_29), B_2) | ~r1_tarski(k3_relat_1(A_29), B_2) | v1_relat_2(A_29) | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.04/1.25  tff(c_28, plain, (![C_16, D_17, A_10]: (r2_hidden(k4_tarski(C_16, D_17), k1_wellord2(A_10)) | ~r1_tarski(C_16, D_17) | ~r2_hidden(D_17, A_10) | ~r2_hidden(C_16, A_10) | ~v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.25  tff(c_168, plain, (![C_54, D_55, A_56]: (r2_hidden(k4_tarski(C_54, D_55), k1_wellord2(A_56)) | ~r1_tarski(C_54, D_55) | ~r2_hidden(D_55, A_56) | ~r2_hidden(C_54, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.04/1.25  tff(c_10, plain, (![A_6]: (~r2_hidden(k4_tarski('#skF_2'(A_6), '#skF_2'(A_6)), A_6) | v1_relat_2(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.25  tff(c_175, plain, (![A_56]: (v1_relat_2(k1_wellord2(A_56)) | ~v1_relat_1(k1_wellord2(A_56)) | ~r1_tarski('#skF_2'(k1_wellord2(A_56)), '#skF_2'(k1_wellord2(A_56))) | ~r2_hidden('#skF_2'(k1_wellord2(A_56)), A_56))), inference(resolution, [status(thm)], [c_168, c_10])).
% 2.04/1.25  tff(c_183, plain, (![A_57]: (v1_relat_2(k1_wellord2(A_57)) | ~r2_hidden('#skF_2'(k1_wellord2(A_57)), A_57))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_32, c_175])).
% 2.04/1.25  tff(c_187, plain, (![B_2]: (~r1_tarski(k3_relat_1(k1_wellord2(B_2)), B_2) | v1_relat_2(k1_wellord2(B_2)) | ~v1_relat_1(k1_wellord2(B_2)))), inference(resolution, [status(thm)], [c_69, c_183])).
% 2.04/1.25  tff(c_197, plain, (![B_2]: (v1_relat_2(k1_wellord2(B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_57, c_40, c_187])).
% 2.04/1.25  tff(c_34, plain, (~v1_relat_2(k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.04/1.25  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_34])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 32
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 0
% 2.04/1.25  #Chain   : 0
% 2.04/1.25  #Close   : 0
% 2.04/1.25  
% 2.04/1.25  Ordering : KBO
% 2.04/1.25  
% 2.04/1.25  Simplification rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Subsume      : 2
% 2.04/1.25  #Demod        : 46
% 2.04/1.25  #Tautology    : 19
% 2.04/1.25  #SimpNegUnit  : 0
% 2.04/1.25  #BackRed      : 1
% 2.04/1.25  
% 2.04/1.25  #Partial instantiations: 0
% 2.04/1.25  #Strategies tried      : 1
% 2.04/1.25  
% 2.04/1.25  Timing (in seconds)
% 2.04/1.25  ----------------------
% 2.04/1.25  Preprocessing        : 0.30
% 2.04/1.25  Parsing              : 0.15
% 2.04/1.25  CNF conversion       : 0.02
% 2.04/1.25  Main loop            : 0.19
% 2.04/1.25  Inferencing          : 0.08
% 2.04/1.25  Reduction            : 0.05
% 2.04/1.25  Demodulation         : 0.04
% 2.04/1.25  BG Simplification    : 0.02
% 2.09/1.25  Subsumption          : 0.04
% 2.09/1.25  Abstraction          : 0.01
% 2.09/1.25  MUC search           : 0.00
% 2.09/1.25  Cooper               : 0.00
% 2.09/1.25  Total                : 0.52
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
