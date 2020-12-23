%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_12,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k10_relat_1(B_6,k9_relat_1(B_6,A_5)),A_5)
      | ~ v2_funct_1(B_6)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k10_relat_1(B_11,k9_relat_1(B_11,A_10)))
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_14,A_15] :
      ( k10_relat_1(B_14,k9_relat_1(B_14,A_15)) = A_15
      | ~ r1_tarski(k10_relat_1(B_14,k9_relat_1(B_14,A_15)),A_15)
      | ~ r1_tarski(A_15,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_47,plain,(
    ! [B_16,A_17] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_16))
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_52,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_59,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_52])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.11  
% 1.54/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.11  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.54/1.11  
% 1.54/1.11  %Foreground sorts:
% 1.54/1.11  
% 1.54/1.11  
% 1.54/1.11  %Background operators:
% 1.54/1.11  
% 1.54/1.11  
% 1.54/1.11  %Foreground operators:
% 1.54/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.54/1.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.54/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.54/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.54/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.54/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.54/1.11  
% 1.54/1.12  tff(f_56, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 1.54/1.12  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 1.54/1.12  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 1.54/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.54/1.12  tff(c_12, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.12  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.12  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.12  tff(c_14, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.12  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.12  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k10_relat_1(B_6, k9_relat_1(B_6, A_5)), A_5) | ~v2_funct_1(B_6) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.54/1.12  tff(c_34, plain, (![A_10, B_11]: (r1_tarski(A_10, k10_relat_1(B_11, k9_relat_1(B_11, A_10))) | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.54/1.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.12  tff(c_42, plain, (![B_14, A_15]: (k10_relat_1(B_14, k9_relat_1(B_14, A_15))=A_15 | ~r1_tarski(k10_relat_1(B_14, k9_relat_1(B_14, A_15)), A_15) | ~r1_tarski(A_15, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.54/1.12  tff(c_47, plain, (![B_16, A_17]: (k10_relat_1(B_16, k9_relat_1(B_16, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_16)) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_10, c_42])).
% 1.54/1.12  tff(c_52, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_47])).
% 1.54/1.12  tff(c_59, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_52])).
% 1.54/1.12  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_59])).
% 1.54/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.12  
% 1.54/1.12  Inference rules
% 1.54/1.12  ----------------------
% 1.54/1.12  #Ref     : 0
% 1.54/1.12  #Sup     : 8
% 1.54/1.12  #Fact    : 0
% 1.54/1.12  #Define  : 0
% 1.54/1.12  #Split   : 1
% 1.54/1.12  #Chain   : 0
% 1.54/1.12  #Close   : 0
% 1.54/1.12  
% 1.54/1.12  Ordering : KBO
% 1.54/1.12  
% 1.54/1.12  Simplification rules
% 1.54/1.12  ----------------------
% 1.54/1.12  #Subsume      : 0
% 1.54/1.12  #Demod        : 5
% 1.54/1.12  #Tautology    : 2
% 1.54/1.12  #SimpNegUnit  : 1
% 1.54/1.12  #BackRed      : 0
% 1.54/1.12  
% 1.54/1.12  #Partial instantiations: 0
% 1.54/1.12  #Strategies tried      : 1
% 1.54/1.12  
% 1.54/1.12  Timing (in seconds)
% 1.54/1.12  ----------------------
% 1.54/1.13  Preprocessing        : 0.26
% 1.54/1.13  Parsing              : 0.15
% 1.54/1.13  CNF conversion       : 0.02
% 1.54/1.13  Main loop            : 0.11
% 1.54/1.13  Inferencing          : 0.04
% 1.54/1.13  Reduction            : 0.03
% 1.54/1.13  Demodulation         : 0.02
% 1.54/1.13  BG Simplification    : 0.01
% 1.54/1.13  Subsumption          : 0.03
% 1.54/1.13  Abstraction          : 0.01
% 1.54/1.13  MUC search           : 0.00
% 1.54/1.13  Cooper               : 0.00
% 1.54/1.13  Total                : 0.39
% 1.54/1.13  Index Insertion      : 0.00
% 1.54/1.13  Index Deletion       : 0.00
% 1.54/1.13  Index Matching       : 0.00
% 1.54/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
