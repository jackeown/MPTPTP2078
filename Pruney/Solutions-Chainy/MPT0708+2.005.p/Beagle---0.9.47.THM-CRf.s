%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:24 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  79 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k10_relat_1(B_12,k9_relat_1(B_12,A_11)))
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,(
    ! [C_31,A_32,D_33,B_34] :
      ( r1_tarski(k10_relat_1(C_31,A_32),k10_relat_1(D_33,B_34))
      | ~ r1_tarski(A_32,B_34)
      | ~ r1_tarski(C_31,D_33)
      | ~ v1_relat_1(D_33)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    ! [A_44,B_46,C_45,A_43,D_47] :
      ( r1_tarski(A_44,k10_relat_1(D_47,B_46))
      | ~ r1_tarski(A_44,k10_relat_1(C_45,A_43))
      | ~ r1_tarski(A_43,B_46)
      | ~ r1_tarski(C_45,D_47)
      | ~ v1_relat_1(D_47)
      | ~ v1_relat_1(C_45) ) ),
    inference(resolution,[status(thm)],[c_121,c_8])).

tff(c_243,plain,(
    ! [A_56,D_57,B_58,B_59] :
      ( r1_tarski(A_56,k10_relat_1(D_57,B_58))
      | ~ r1_tarski(k9_relat_1(B_59,A_56),B_58)
      | ~ r1_tarski(B_59,D_57)
      | ~ v1_relat_1(D_57)
      | ~ r1_tarski(A_56,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_12,c_183])).

tff(c_259,plain,(
    ! [D_57] :
      ( r1_tarski('#skF_1',k10_relat_1(D_57,'#skF_2'))
      | ~ r1_tarski('#skF_3',D_57)
      | ~ v1_relat_1(D_57)
      | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_243])).

tff(c_274,plain,(
    ! [D_60] :
      ( r1_tarski('#skF_1',k10_relat_1(D_60,'#skF_2'))
      | ~ r1_tarski('#skF_3',D_60)
      | ~ v1_relat_1(D_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_259])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_287,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_14])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.35  
% 1.95/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.36  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.36  
% 1.95/1.36  %Foreground sorts:
% 1.95/1.36  
% 1.95/1.36  
% 1.95/1.36  %Background operators:
% 1.95/1.36  
% 1.95/1.36  
% 1.95/1.36  %Foreground operators:
% 1.95/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.36  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.36  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.36  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.36  
% 2.41/1.37  tff(f_65, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.41/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.37  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.41/1.37  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t180_relat_1)).
% 2.41/1.37  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.41/1.37  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.37  tff(c_18, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.37  tff(c_16, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.37  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, k10_relat_1(B_12, k9_relat_1(B_12, A_11))) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.37  tff(c_121, plain, (![C_31, A_32, D_33, B_34]: (r1_tarski(k10_relat_1(C_31, A_32), k10_relat_1(D_33, B_34)) | ~r1_tarski(A_32, B_34) | ~r1_tarski(C_31, D_33) | ~v1_relat_1(D_33) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.37  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.37  tff(c_183, plain, (![A_44, B_46, C_45, A_43, D_47]: (r1_tarski(A_44, k10_relat_1(D_47, B_46)) | ~r1_tarski(A_44, k10_relat_1(C_45, A_43)) | ~r1_tarski(A_43, B_46) | ~r1_tarski(C_45, D_47) | ~v1_relat_1(D_47) | ~v1_relat_1(C_45))), inference(resolution, [status(thm)], [c_121, c_8])).
% 2.41/1.37  tff(c_243, plain, (![A_56, D_57, B_58, B_59]: (r1_tarski(A_56, k10_relat_1(D_57, B_58)) | ~r1_tarski(k9_relat_1(B_59, A_56), B_58) | ~r1_tarski(B_59, D_57) | ~v1_relat_1(D_57) | ~r1_tarski(A_56, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_12, c_183])).
% 2.41/1.37  tff(c_259, plain, (![D_57]: (r1_tarski('#skF_1', k10_relat_1(D_57, '#skF_2')) | ~r1_tarski('#skF_3', D_57) | ~v1_relat_1(D_57) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_243])).
% 2.41/1.37  tff(c_274, plain, (![D_60]: (r1_tarski('#skF_1', k10_relat_1(D_60, '#skF_2')) | ~r1_tarski('#skF_3', D_60) | ~v1_relat_1(D_60))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_259])).
% 2.41/1.37  tff(c_14, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.37  tff(c_287, plain, (~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_274, c_14])).
% 2.41/1.37  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_287])).
% 2.41/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.37  
% 2.41/1.37  Inference rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Ref     : 0
% 2.41/1.37  #Sup     : 70
% 2.41/1.37  #Fact    : 0
% 2.41/1.37  #Define  : 0
% 2.41/1.37  #Split   : 3
% 2.41/1.37  #Chain   : 0
% 2.41/1.37  #Close   : 0
% 2.41/1.37  
% 2.41/1.37  Ordering : KBO
% 2.41/1.37  
% 2.41/1.37  Simplification rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Subsume      : 10
% 2.41/1.37  #Demod        : 12
% 2.41/1.37  #Tautology    : 6
% 2.41/1.37  #SimpNegUnit  : 0
% 2.41/1.37  #BackRed      : 0
% 2.41/1.37  
% 2.41/1.37  #Partial instantiations: 0
% 2.41/1.37  #Strategies tried      : 1
% 2.41/1.37  
% 2.41/1.37  Timing (in seconds)
% 2.41/1.37  ----------------------
% 2.41/1.37  Preprocessing        : 0.24
% 2.41/1.37  Parsing              : 0.13
% 2.41/1.37  CNF conversion       : 0.02
% 2.41/1.37  Main loop            : 0.27
% 2.41/1.37  Inferencing          : 0.09
% 2.41/1.37  Reduction            : 0.07
% 2.41/1.37  Demodulation         : 0.05
% 2.41/1.37  BG Simplification    : 0.01
% 2.41/1.37  Subsumption          : 0.08
% 2.41/1.37  Abstraction          : 0.01
% 2.41/1.37  MUC search           : 0.00
% 2.41/1.37  Cooper               : 0.00
% 2.41/1.37  Total                : 0.54
% 2.41/1.37  Index Insertion      : 0.00
% 2.41/1.37  Index Deletion       : 0.00
% 2.41/1.37  Index Matching       : 0.00
% 2.41/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
