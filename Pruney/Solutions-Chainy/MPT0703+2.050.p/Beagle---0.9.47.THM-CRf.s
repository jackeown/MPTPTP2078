%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  91 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    ! [B_17,A_18] :
      ( k9_relat_1(B_17,k10_relat_1(B_17,A_18)) = A_18
      | ~ r1_tarski(A_18,k2_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_26,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_23])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k9_relat_1(C_6,A_4),k9_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_5] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_5))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_5)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_41,plain,(
    ! [B_19] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_19))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_45,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_51,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,k9_relat_1(B_22,k1_relat_1(B_22))) = k9_relat_1(B_22,k10_relat_1(B_22,A_21))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_23,A_24,B_25] :
      ( r1_tarski(A_23,A_24)
      | ~ r1_tarski(A_23,k9_relat_1(B_25,k10_relat_1(B_25,A_24)))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_2])).

tff(c_66,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_63])).

tff(c_76,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_66])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.50  
% 2.09/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.50  
% 2.09/1.50  %Foreground sorts:
% 2.09/1.50  
% 2.09/1.50  
% 2.09/1.50  %Background operators:
% 2.09/1.50  
% 2.09/1.50  
% 2.09/1.50  %Foreground operators:
% 2.09/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.50  
% 2.14/1.52  tff(f_60, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.14/1.52  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.14/1.52  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.14/1.52  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 2.14/1.52  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.14/1.52  tff(c_10, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.52  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.52  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.52  tff(c_14, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.52  tff(c_12, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.52  tff(c_21, plain, (![B_17, A_18]: (k9_relat_1(B_17, k10_relat_1(B_17, A_18))=A_18 | ~r1_tarski(A_18, k2_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.52  tff(c_23, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_21])).
% 2.14/1.52  tff(c_26, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_23])).
% 2.14/1.52  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k9_relat_1(C_6, A_4), k9_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.52  tff(c_30, plain, (![B_5]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_5)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_5) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 2.14/1.52  tff(c_41, plain, (![B_19]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_19)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 2.14/1.52  tff(c_45, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_14, c_41])).
% 2.14/1.52  tff(c_51, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k9_relat_1(B_22, k1_relat_1(B_22)))=k9_relat_1(B_22, k10_relat_1(B_22, A_21)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.52  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.52  tff(c_63, plain, (![A_23, A_24, B_25]: (r1_tarski(A_23, A_24) | ~r1_tarski(A_23, k9_relat_1(B_25, k10_relat_1(B_25, A_24))) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_51, c_2])).
% 2.14/1.52  tff(c_66, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_45, c_63])).
% 2.14/1.52  tff(c_76, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_66])).
% 2.14/1.52  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_76])).
% 2.14/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.52  
% 2.14/1.52  Inference rules
% 2.14/1.52  ----------------------
% 2.14/1.52  #Ref     : 0
% 2.14/1.52  #Sup     : 13
% 2.14/1.52  #Fact    : 0
% 2.14/1.52  #Define  : 0
% 2.14/1.52  #Split   : 1
% 2.14/1.52  #Chain   : 0
% 2.14/1.52  #Close   : 0
% 2.14/1.52  
% 2.14/1.52  Ordering : KBO
% 2.14/1.52  
% 2.14/1.52  Simplification rules
% 2.14/1.52  ----------------------
% 2.14/1.52  #Subsume      : 0
% 2.14/1.52  #Demod        : 6
% 2.14/1.52  #Tautology    : 4
% 2.14/1.52  #SimpNegUnit  : 1
% 2.14/1.52  #BackRed      : 0
% 2.14/1.52  
% 2.14/1.52  #Partial instantiations: 0
% 2.14/1.52  #Strategies tried      : 1
% 2.14/1.52  
% 2.14/1.52  Timing (in seconds)
% 2.14/1.52  ----------------------
% 2.14/1.52  Preprocessing        : 0.41
% 2.14/1.52  Parsing              : 0.23
% 2.14/1.52  CNF conversion       : 0.03
% 2.14/1.52  Main loop            : 0.20
% 2.14/1.52  Inferencing          : 0.09
% 2.14/1.52  Reduction            : 0.05
% 2.14/1.53  Demodulation         : 0.04
% 2.14/1.53  BG Simplification    : 0.01
% 2.14/1.53  Subsumption          : 0.03
% 2.14/1.53  Abstraction          : 0.01
% 2.14/1.53  MUC search           : 0.00
% 2.14/1.53  Cooper               : 0.00
% 2.14/1.53  Total                : 0.66
% 2.14/1.53  Index Insertion      : 0.00
% 2.14/1.53  Index Deletion       : 0.00
% 2.14/1.53  Index Matching       : 0.00
% 2.14/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
