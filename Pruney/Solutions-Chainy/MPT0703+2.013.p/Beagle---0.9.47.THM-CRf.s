%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:10 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 101 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_226,plain,(
    ! [B_34,A_35] :
      ( k9_relat_1(B_34,k10_relat_1(B_34,A_35)) = A_35
      | ~ r1_tarski(A_35,k2_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_233,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_226])).

tff(c_240,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_233])).

tff(c_404,plain,(
    ! [C_45,A_46,B_47] :
      ( k3_xboole_0(k10_relat_1(C_45,A_46),k10_relat_1(C_45,B_47)) = k10_relat_1(C_45,k3_xboole_0(A_46,B_47))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_6])).

tff(c_420,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_68])).

tff(c_444,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_420])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,k10_relat_1(B_12,A_11)),A_11)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_463,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_10])).

tff(c_474,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_240,c_463])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,B_20)
      | ~ r1_tarski(A_19,k3_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_19,A_1,B_2] :
      ( r1_tarski(A_19,A_1)
      | ~ r1_tarski(A_19,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_480,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_474,c_75])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.33  
% 2.42/1.34  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.42/1.34  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.42/1.34  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 2.42/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.42/1.34  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 2.42/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.42/1.34  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.42/1.34  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_226, plain, (![B_34, A_35]: (k9_relat_1(B_34, k10_relat_1(B_34, A_35))=A_35 | ~r1_tarski(A_35, k2_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.34  tff(c_233, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_226])).
% 2.42/1.34  tff(c_240, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_233])).
% 2.42/1.34  tff(c_404, plain, (![C_45, A_46, B_47]: (k3_xboole_0(k10_relat_1(C_45, A_46), k10_relat_1(C_45, B_47))=k10_relat_1(C_45, k3_xboole_0(A_46, B_47)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.34  tff(c_18, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.34  tff(c_68, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_6])).
% 2.42/1.34  tff(c_420, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_404, c_68])).
% 2.42/1.34  tff(c_444, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_420])).
% 2.42/1.34  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, k10_relat_1(B_12, A_11)), A_11) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.34  tff(c_463, plain, (r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_444, c_10])).
% 2.42/1.34  tff(c_474, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_240, c_463])).
% 2.42/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.34  tff(c_69, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, B_20) | ~r1_tarski(A_19, k3_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.34  tff(c_75, plain, (![A_19, A_1, B_2]: (r1_tarski(A_19, A_1) | ~r1_tarski(A_19, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 2.42/1.34  tff(c_480, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_474, c_75])).
% 2.42/1.34  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_480])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 125
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 1
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 20
% 2.42/1.34  #Demod        : 54
% 2.42/1.34  #Tautology    : 48
% 2.42/1.34  #SimpNegUnit  : 1
% 2.42/1.34  #BackRed      : 0
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.34  Preprocessing        : 0.29
% 2.42/1.34  Parsing              : 0.17
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.27
% 2.42/1.34  Inferencing          : 0.10
% 2.42/1.34  Reduction            : 0.08
% 2.42/1.34  Demodulation         : 0.06
% 2.42/1.34  BG Simplification    : 0.01
% 2.42/1.34  Subsumption          : 0.06
% 2.42/1.35  Abstraction          : 0.01
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.59
% 2.42/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
