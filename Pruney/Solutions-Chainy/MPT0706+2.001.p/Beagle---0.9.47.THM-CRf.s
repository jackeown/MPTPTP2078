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
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 120 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k10_relat_1(C,A) = k10_relat_1(C,B)
            & r1_tarski(A,k2_relat_1(C))
            & r1_tarski(B,k2_relat_1(C)) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
          & r1_tarski(A,k2_relat_1(C)) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    k10_relat_1('#skF_3','#skF_2') = k10_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_tarski(A_9,k2_relat_1(C_11))
      | ~ r1_tarski(k10_relat_1(C_11,A_9),k10_relat_1(C_11,B_10))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_2',B_10)
      | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',B_10))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_59,plain,(
    ! [B_12] :
      ( r1_tarski('#skF_2',B_12)
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',B_12)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_12,c_45])).

tff(c_69,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,'#skF_2')
      | ~ r1_tarski(A_9,k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3',A_9),k10_relat_1('#skF_3','#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_75,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,'#skF_2')
      | ~ r1_tarski(A_13,k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3',A_13),k10_relat_1('#skF_3','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_48])).

tff(c_82,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_87,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_92,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:18:17 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  
% 1.88/1.23  tff(f_54, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k10_relat_1(C, A) = k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) & r1_tarski(B, k2_relat_1(C))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_funct_1)).
% 1.88/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.23  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 1.88/1.23  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.23  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_12, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_16, plain, (k10_relat_1('#skF_3', '#skF_2')=k10_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_42, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, B_10) | ~r1_tarski(A_9, k2_relat_1(C_11)) | ~r1_tarski(k10_relat_1(C_11, A_9), k10_relat_1(C_11, B_10)) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.23  tff(c_45, plain, (![B_10]: (r1_tarski('#skF_2', B_10) | ~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', B_10)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_42])).
% 1.88/1.23  tff(c_59, plain, (![B_12]: (r1_tarski('#skF_2', B_12) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_12, c_45])).
% 1.88/1.23  tff(c_69, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.88/1.23  tff(c_14, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_48, plain, (![A_9]: (r1_tarski(A_9, '#skF_2') | ~r1_tarski(A_9, k2_relat_1('#skF_3')) | ~r1_tarski(k10_relat_1('#skF_3', A_9), k10_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_42])).
% 1.88/1.23  tff(c_75, plain, (![A_13]: (r1_tarski(A_13, '#skF_2') | ~r1_tarski(A_13, k2_relat_1('#skF_3')) | ~r1_tarski(k10_relat_1('#skF_3', A_13), k10_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_48])).
% 1.88/1.23  tff(c_82, plain, (r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_75])).
% 1.88/1.23  tff(c_87, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 1.88/1.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.23  tff(c_89, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_2])).
% 1.88/1.23  tff(c_92, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_89])).
% 1.88/1.23  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_92])).
% 1.88/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  Inference rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Ref     : 0
% 1.88/1.23  #Sup     : 14
% 1.88/1.23  #Fact    : 0
% 1.88/1.23  #Define  : 0
% 1.88/1.23  #Split   : 2
% 1.88/1.23  #Chain   : 0
% 1.88/1.23  #Close   : 0
% 1.88/1.23  
% 1.88/1.23  Ordering : KBO
% 1.88/1.23  
% 1.88/1.23  Simplification rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Subsume      : 0
% 1.88/1.23  #Demod        : 15
% 1.88/1.23  #Tautology    : 7
% 1.88/1.23  #SimpNegUnit  : 2
% 1.88/1.23  #BackRed      : 0
% 1.88/1.23  
% 1.88/1.23  #Partial instantiations: 0
% 1.88/1.23  #Strategies tried      : 1
% 1.88/1.23  
% 1.88/1.23  Timing (in seconds)
% 1.88/1.23  ----------------------
% 1.88/1.23  Preprocessing        : 0.30
% 1.88/1.23  Parsing              : 0.16
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.12
% 1.88/1.23  Inferencing          : 0.04
% 1.88/1.23  Reduction            : 0.04
% 1.88/1.23  Demodulation         : 0.03
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.03
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.45
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
