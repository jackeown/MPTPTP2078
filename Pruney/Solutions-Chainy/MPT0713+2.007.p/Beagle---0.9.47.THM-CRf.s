%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  67 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_8,A_9] :
      ( k2_relat_1(k7_relat_1(B_8,A_9)) = k9_relat_1(B_8,A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_36,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_12,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [C_10,A_11,B_12] :
      ( k2_tarski(k1_funct_1(C_10,A_11),k1_funct_1(C_10,B_12)) = k9_relat_1(C_10,k2_tarski(A_11,B_12))
      | ~ r2_hidden(B_12,k1_relat_1(C_10))
      | ~ r2_hidden(A_11,k1_relat_1(C_10))
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [C_10,B_12] :
      ( k9_relat_1(C_10,k2_tarski(B_12,B_12)) = k1_tarski(k1_funct_1(C_10,B_12))
      | ~ r2_hidden(B_12,k1_relat_1(C_10))
      | ~ r2_hidden(B_12,k1_relat_1(C_10))
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_57,plain,(
    ! [C_13,B_14] :
      ( k9_relat_1(C_13,k1_tarski(B_14)) = k1_tarski(k1_funct_1(C_13,B_14))
      | ~ r2_hidden(B_14,k1_relat_1(C_13))
      | ~ r2_hidden(B_14,k1_relat_1(C_13))
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_59,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_62,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_59])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.40  
% 2.06/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.41  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.06/1.41  
% 2.06/1.41  %Foreground sorts:
% 2.06/1.41  
% 2.06/1.41  
% 2.06/1.41  %Background operators:
% 2.06/1.41  
% 2.06/1.41  
% 2.06/1.41  %Foreground operators:
% 2.06/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.41  
% 2.06/1.42  tff(f_50, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 2.06/1.42  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.06/1.42  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.42  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 2.06/1.42  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.42  tff(c_24, plain, (![B_8, A_9]: (k2_relat_1(k7_relat_1(B_8, A_9))=k9_relat_1(B_8, A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.42  tff(c_8, plain, (k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1')))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.42  tff(c_30, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_8])).
% 2.06/1.42  tff(c_36, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 2.06/1.42  tff(c_12, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.42  tff(c_10, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.42  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.42  tff(c_38, plain, (![C_10, A_11, B_12]: (k2_tarski(k1_funct_1(C_10, A_11), k1_funct_1(C_10, B_12))=k9_relat_1(C_10, k2_tarski(A_11, B_12)) | ~r2_hidden(B_12, k1_relat_1(C_10)) | ~r2_hidden(A_11, k1_relat_1(C_10)) | ~v1_funct_1(C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.42  tff(c_45, plain, (![C_10, B_12]: (k9_relat_1(C_10, k2_tarski(B_12, B_12))=k1_tarski(k1_funct_1(C_10, B_12)) | ~r2_hidden(B_12, k1_relat_1(C_10)) | ~r2_hidden(B_12, k1_relat_1(C_10)) | ~v1_funct_1(C_10) | ~v1_relat_1(C_10))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 2.06/1.42  tff(c_57, plain, (![C_13, B_14]: (k9_relat_1(C_13, k1_tarski(B_14))=k1_tarski(k1_funct_1(C_13, B_14)) | ~r2_hidden(B_14, k1_relat_1(C_13)) | ~r2_hidden(B_14, k1_relat_1(C_13)) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 2.06/1.42  tff(c_59, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_57])).
% 2.06/1.42  tff(c_62, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_10, c_59])).
% 2.06/1.42  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_62])).
% 2.06/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.42  
% 2.06/1.42  Inference rules
% 2.06/1.42  ----------------------
% 2.06/1.42  #Ref     : 0
% 2.06/1.42  #Sup     : 10
% 2.06/1.42  #Fact    : 0
% 2.06/1.42  #Define  : 0
% 2.06/1.42  #Split   : 0
% 2.06/1.42  #Chain   : 0
% 2.06/1.42  #Close   : 0
% 2.06/1.42  
% 2.06/1.42  Ordering : KBO
% 2.06/1.42  
% 2.06/1.42  Simplification rules
% 2.06/1.42  ----------------------
% 2.06/1.42  #Subsume      : 0
% 2.06/1.42  #Demod        : 6
% 2.06/1.42  #Tautology    : 6
% 2.06/1.42  #SimpNegUnit  : 1
% 2.06/1.42  #BackRed      : 0
% 2.06/1.42  
% 2.06/1.42  #Partial instantiations: 0
% 2.06/1.42  #Strategies tried      : 1
% 2.06/1.42  
% 2.06/1.42  Timing (in seconds)
% 2.06/1.42  ----------------------
% 2.06/1.43  Preprocessing        : 0.45
% 2.06/1.43  Parsing              : 0.24
% 2.06/1.43  CNF conversion       : 0.03
% 2.06/1.43  Main loop            : 0.14
% 2.06/1.43  Inferencing          : 0.06
% 2.06/1.43  Reduction            : 0.04
% 2.06/1.43  Demodulation         : 0.04
% 2.06/1.43  BG Simplification    : 0.01
% 2.06/1.43  Subsumption          : 0.01
% 2.06/1.43  Abstraction          : 0.01
% 2.06/1.43  MUC search           : 0.00
% 2.06/1.43  Cooper               : 0.00
% 2.06/1.43  Total                : 0.64
% 2.06/1.43  Index Insertion      : 0.00
% 2.06/1.43  Index Deletion       : 0.00
% 2.06/1.43  Index Matching       : 0.00
% 2.06/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
