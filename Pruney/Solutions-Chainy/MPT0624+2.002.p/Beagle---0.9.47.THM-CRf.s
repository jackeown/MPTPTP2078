%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  99 expanded)
%              Number of equality atoms :    2 (   7 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & ! [D] :
                    ~ ( r2_hidden(D,k1_relat_1(B))
                      & C = k1_funct_1(B,D) ) )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_1'(A_15,B_16),B_16)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

tff(c_18,plain,(
    ! [C_11] :
      ( r2_hidden('#skF_4'(C_11),k1_relat_1('#skF_3'))
      | ~ r2_hidden(C_11,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_37,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [C_11,B_21] :
      ( r2_hidden('#skF_4'(C_11),B_21)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_21)
      | ~ r2_hidden(C_11,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [C_11] :
      ( k1_funct_1('#skF_3','#skF_4'(C_11)) = C_11
      | ~ r2_hidden(C_11,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(k1_funct_1(B_28,A_29),k2_relat_1(B_28))
      | ~ r2_hidden(A_29,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [C_11] :
      ( r2_hidden(C_11,k2_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'(C_11),k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden(C_11,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_66,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k2_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'(C_30),k1_relat_1('#skF_3'))
      | ~ r2_hidden(C_30,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_62])).

tff(c_70,plain,(
    ! [C_11] :
      ( r2_hidden(C_11,k2_relat_1('#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ r2_hidden(C_11,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_78,plain,(
    ! [C_31] :
      ( r2_hidden(C_31,k2_relat_1('#skF_3'))
      | ~ r2_hidden(C_31,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,k2_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_37,k2_relat_1('#skF_3')),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_109,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_10,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.72/1.16  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.16  
% 1.72/1.17  tff(f_57, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_funct_1)).
% 1.72/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.72/1.17  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.72/1.17  tff(c_10, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.17  tff(c_20, plain, (![A_15, B_16]: (~r2_hidden('#skF_1'(A_15, B_16), B_16) | r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.17  tff(c_25, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_20])).
% 1.72/1.17  tff(c_18, plain, (![C_11]: (r2_hidden('#skF_4'(C_11), k1_relat_1('#skF_3')) | ~r2_hidden(C_11, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_37, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.17  tff(c_42, plain, (![C_11, B_21]: (r2_hidden('#skF_4'(C_11), B_21) | ~r1_tarski(k1_relat_1('#skF_3'), B_21) | ~r2_hidden(C_11, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_37])).
% 1.72/1.17  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_16, plain, (![C_11]: (k1_funct_1('#skF_3', '#skF_4'(C_11))=C_11 | ~r2_hidden(C_11, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.17  tff(c_57, plain, (![B_28, A_29]: (r2_hidden(k1_funct_1(B_28, A_29), k2_relat_1(B_28)) | ~r2_hidden(A_29, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.17  tff(c_62, plain, (![C_11]: (r2_hidden(C_11, k2_relat_1('#skF_3')) | ~r2_hidden('#skF_4'(C_11), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r2_hidden(C_11, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 1.72/1.17  tff(c_66, plain, (![C_30]: (r2_hidden(C_30, k2_relat_1('#skF_3')) | ~r2_hidden('#skF_4'(C_30), k1_relat_1('#skF_3')) | ~r2_hidden(C_30, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_62])).
% 1.72/1.17  tff(c_70, plain, (![C_11]: (r2_hidden(C_11, k2_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~r2_hidden(C_11, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_66])).
% 1.72/1.17  tff(c_78, plain, (![C_31]: (r2_hidden(C_31, k2_relat_1('#skF_3')) | ~r2_hidden(C_31, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_70])).
% 1.72/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.17  tff(c_101, plain, (![A_37]: (r1_tarski(A_37, k2_relat_1('#skF_3')) | ~r2_hidden('#skF_1'(A_37, k2_relat_1('#skF_3')), '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_4])).
% 1.72/1.17  tff(c_109, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_101])).
% 1.72/1.17  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_10, c_109])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 19
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 3
% 1.72/1.17  #Demod        : 5
% 1.72/1.17  #Tautology    : 3
% 1.72/1.17  #SimpNegUnit  : 1
% 1.72/1.17  #BackRed      : 0
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.95/1.18  Preprocessing        : 0.27
% 1.95/1.18  Parsing              : 0.15
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.15
% 1.95/1.18  Inferencing          : 0.07
% 1.95/1.18  Reduction            : 0.03
% 1.95/1.18  Demodulation         : 0.02
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.03
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.44
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
