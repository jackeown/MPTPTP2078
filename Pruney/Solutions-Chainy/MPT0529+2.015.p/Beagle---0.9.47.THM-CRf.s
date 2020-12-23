%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:13 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  87 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_57,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(A_25,B_26)
      | ~ r2_hidden(A_25,k2_relat_1(k8_relat_1(B_26,C_27)))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [B_54,C_55,B_56] :
      ( r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_54,C_55)),B_56),B_54)
      | ~ v1_relat_1(C_55)
      | r1_tarski(k2_relat_1(k8_relat_1(B_54,C_55)),B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    ! [C_57,B_58] :
      ( ~ v1_relat_1(C_57)
      | r1_tarski(k2_relat_1(k8_relat_1(B_58,C_57)),B_58) ) ),
    inference(resolution,[status(thm)],[c_165,c_4])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_29,B_30,B_31] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(A_29,B_31)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_35,B_36,B_37,B_38] :
      ( r2_hidden('#skF_1'(A_35,B_36),B_37)
      | ~ r1_tarski(B_38,B_37)
      | ~ r1_tarski(A_35,B_38)
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_98,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),'#skF_3')
      | ~ r1_tarski(A_39,'#skF_2')
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_106,plain,(
    ! [A_39] :
      ( ~ r1_tarski(A_39,'#skF_2')
      | r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_207,plain,(
    ! [C_59] :
      ( r1_tarski(k2_relat_1(k8_relat_1('#skF_2',C_59)),'#skF_3')
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_187,c_106])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [C_69] :
      ( k8_relat_1('#skF_3',k8_relat_1('#skF_2',C_69)) = k8_relat_1('#skF_2',C_69)
      | ~ v1_relat_1(k8_relat_1('#skF_2',C_69))
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_207,c_16])).

tff(c_321,plain,(
    ! [B_70] :
      ( k8_relat_1('#skF_3',k8_relat_1('#skF_2',B_70)) = k8_relat_1('#skF_2',B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_8,c_311])).

tff(c_18,plain,(
    k8_relat_1('#skF_3',k8_relat_1('#skF_2','#skF_4')) != k8_relat_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_351,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_18])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.28  
% 2.14/1.30  tff(f_57, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.14/1.30  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.14/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.14/1.30  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_relat_1)).
% 2.14/1.30  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.14/1.30  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.30  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_42, plain, (![A_25, B_26, C_27]: (r2_hidden(A_25, B_26) | ~r2_hidden(A_25, k2_relat_1(k8_relat_1(B_26, C_27))) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.30  tff(c_165, plain, (![B_54, C_55, B_56]: (r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_54, C_55)), B_56), B_54) | ~v1_relat_1(C_55) | r1_tarski(k2_relat_1(k8_relat_1(B_54, C_55)), B_56))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.14/1.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_187, plain, (![C_57, B_58]: (~v1_relat_1(C_57) | r1_tarski(k2_relat_1(k8_relat_1(B_58, C_57)), B_58))), inference(resolution, [status(thm)], [c_165, c_4])).
% 2.14/1.30  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.30  tff(c_32, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_63, plain, (![A_29, B_30, B_31]: (r2_hidden('#skF_1'(A_29, B_30), B_31) | ~r1_tarski(A_29, B_31) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_6, c_32])).
% 2.14/1.30  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_91, plain, (![A_35, B_36, B_37, B_38]: (r2_hidden('#skF_1'(A_35, B_36), B_37) | ~r1_tarski(B_38, B_37) | ~r1_tarski(A_35, B_38) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.14/1.30  tff(c_98, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), '#skF_3') | ~r1_tarski(A_39, '#skF_2') | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_20, c_91])).
% 2.14/1.30  tff(c_106, plain, (![A_39]: (~r1_tarski(A_39, '#skF_2') | r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_4])).
% 2.14/1.30  tff(c_207, plain, (![C_59]: (r1_tarski(k2_relat_1(k8_relat_1('#skF_2', C_59)), '#skF_3') | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_187, c_106])).
% 2.14/1.30  tff(c_16, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.30  tff(c_311, plain, (![C_69]: (k8_relat_1('#skF_3', k8_relat_1('#skF_2', C_69))=k8_relat_1('#skF_2', C_69) | ~v1_relat_1(k8_relat_1('#skF_2', C_69)) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_207, c_16])).
% 2.14/1.30  tff(c_321, plain, (![B_70]: (k8_relat_1('#skF_3', k8_relat_1('#skF_2', B_70))=k8_relat_1('#skF_2', B_70) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_8, c_311])).
% 2.14/1.30  tff(c_18, plain, (k8_relat_1('#skF_3', k8_relat_1('#skF_2', '#skF_4'))!=k8_relat_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.30  tff(c_351, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_321, c_18])).
% 2.14/1.30  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_351])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 84
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 0
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 12
% 2.14/1.30  #Demod        : 6
% 2.14/1.30  #Tautology    : 25
% 2.14/1.30  #SimpNegUnit  : 0
% 2.14/1.30  #BackRed      : 0
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.27
% 2.14/1.30  Parsing              : 0.15
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.26
% 2.14/1.30  Inferencing          : 0.11
% 2.14/1.30  Reduction            : 0.06
% 2.14/1.30  Demodulation         : 0.04
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.06
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.56
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
