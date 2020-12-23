%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(k1_funct_1(B_28,A_29),k2_relat_1(B_28))
      | ~ r2_hidden(A_29,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [B_30,A_31,B_32] :
      ( r2_hidden(k1_funct_1(B_30,A_31),B_32)
      | ~ r1_tarski(k2_relat_1(B_30),B_32)
      | ~ r2_hidden(A_31,k1_relat_1(B_30))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_75,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_14])).

tff(c_79,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_16,c_75])).

tff(c_82,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.65/1.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.12  
% 1.65/1.13  tff(f_58, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 1.65/1.13  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.65/1.13  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.65/1.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.65/1.13  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.13  tff(c_20, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.13  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.13  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.13  tff(c_16, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.13  tff(c_66, plain, (![B_28, A_29]: (r2_hidden(k1_funct_1(B_28, A_29), k2_relat_1(B_28)) | ~r2_hidden(A_29, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.13  tff(c_70, plain, (![B_30, A_31, B_32]: (r2_hidden(k1_funct_1(B_30, A_31), B_32) | ~r1_tarski(k2_relat_1(B_30), B_32) | ~r2_hidden(A_31, k1_relat_1(B_30)) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_66, c_2])).
% 1.65/1.13  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.13  tff(c_75, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r2_hidden('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_14])).
% 1.65/1.13  tff(c_79, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_16, c_75])).
% 1.65/1.13  tff(c_82, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_79])).
% 1.65/1.13  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_82])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 12
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 0
% 1.65/1.13  #Demod        : 6
% 1.65/1.13  #Tautology    : 3
% 1.65/1.13  #SimpNegUnit  : 0
% 1.65/1.13  #BackRed      : 0
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.14  Preprocessing        : 0.26
% 1.65/1.14  Parsing              : 0.14
% 1.65/1.14  CNF conversion       : 0.02
% 1.65/1.14  Main loop            : 0.13
% 1.65/1.14  Inferencing          : 0.06
% 1.65/1.14  Reduction            : 0.03
% 1.65/1.14  Demodulation         : 0.02
% 1.65/1.14  BG Simplification    : 0.01
% 1.65/1.14  Subsumption          : 0.02
% 1.65/1.14  Abstraction          : 0.00
% 1.65/1.14  MUC search           : 0.00
% 1.65/1.14  Cooper               : 0.00
% 1.65/1.14  Total                : 0.41
% 1.65/1.14  Index Insertion      : 0.00
% 1.65/1.14  Index Deletion       : 0.00
% 1.65/1.14  Index Matching       : 0.00
% 1.65/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
