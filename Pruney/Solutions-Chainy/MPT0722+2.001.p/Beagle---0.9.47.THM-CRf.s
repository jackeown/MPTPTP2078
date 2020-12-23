%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  97 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [B_15,A_16] :
      ( k9_relat_1(k2_funct_1(B_15),A_16) = k10_relat_1(B_15,A_16)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_55,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_49])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k10_relat_1(B_4,k9_relat_1(B_4,A_3)))
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [B_13,A_14] :
      ( r1_tarski(k10_relat_1(B_13,k9_relat_1(B_13,A_14)),A_14)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_19,A_20] :
      ( k10_relat_1(B_19,k9_relat_1(B_19,A_20)) = A_20
      | ~ r1_tarski(A_20,k10_relat_1(B_19,k9_relat_1(B_19,A_20)))
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_72,plain,(
    ! [B_21,A_22] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,A_22)) = A_22
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ r1_tarski(A_22,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_77,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_84,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_77])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:30:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.65/1.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_65, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 1.65/1.12  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 1.65/1.12  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 1.65/1.12  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 1.65/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.65/1.12  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.12  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.12  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.12  tff(c_40, plain, (![B_15, A_16]: (k9_relat_1(k2_funct_1(B_15), A_16)=k10_relat_1(B_15, A_16) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.65/1.12  tff(c_14, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.12  tff(c_49, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_14])).
% 1.65/1.12  tff(c_55, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_49])).
% 1.65/1.12  tff(c_16, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.12  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k10_relat_1(B_4, k9_relat_1(B_4, A_3))) | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.12  tff(c_36, plain, (![B_13, A_14]: (r1_tarski(k10_relat_1(B_13, k9_relat_1(B_13, A_14)), A_14) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.12  tff(c_64, plain, (![B_19, A_20]: (k10_relat_1(B_19, k9_relat_1(B_19, A_20))=A_20 | ~r1_tarski(A_20, k10_relat_1(B_19, k9_relat_1(B_19, A_20))) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.65/1.12  tff(c_72, plain, (![B_21, A_22]: (k10_relat_1(B_21, k9_relat_1(B_21, A_22))=A_22 | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~r1_tarski(A_22, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_8, c_64])).
% 1.65/1.12  tff(c_77, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_72])).
% 1.65/1.12  tff(c_84, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_77])).
% 1.65/1.12  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_84])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 14
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 1
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 8
% 1.65/1.12  #Tautology    : 4
% 1.65/1.12  #SimpNegUnit  : 1
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.26
% 1.65/1.13  Parsing              : 0.14
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.13
% 1.65/1.13  Inferencing          : 0.05
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.03
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.03
% 1.65/1.13  Abstraction          : 0.01
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.41
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
