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
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  57 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_12,B_13] :
      ( k9_relat_1(A_12,k1_tarski(B_13)) = k11_relat_1(A_12,B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_39,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_37])).

tff(c_46,plain,
    ( k1_tarski(k1_funct_1('#skF_2','#skF_1')) != k11_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_39])).

tff(c_52,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) != k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_14,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [B_14,A_15] :
      ( k1_tarski(k1_funct_1(B_14,A_15)) = k11_relat_1(B_14,A_15)
      | ~ r2_hidden(A_15,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,
    ( k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_60,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_57])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.81/1.23  
% 1.81/1.23  %Foreground sorts:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Background operators:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Foreground operators:
% 1.81/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.23  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.81/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.23  
% 1.90/1.24  tff(f_53, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 1.90/1.24  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 1.90/1.24  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.90/1.24  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 1.90/1.24  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.24  tff(c_40, plain, (![A_12, B_13]: (k9_relat_1(A_12, k1_tarski(B_13))=k11_relat_1(A_12, B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.24  tff(c_6, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.24  tff(c_10, plain, (k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1')))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.24  tff(c_37, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_10])).
% 1.90/1.24  tff(c_39, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_37])).
% 1.90/1.24  tff(c_46, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))!=k11_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_40, c_39])).
% 1.90/1.24  tff(c_52, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))!=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 1.90/1.24  tff(c_14, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.24  tff(c_12, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.24  tff(c_54, plain, (![B_14, A_15]: (k1_tarski(k1_funct_1(B_14, A_15))=k11_relat_1(B_14, A_15) | ~r2_hidden(A_15, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.24  tff(c_57, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_54])).
% 1.90/1.24  tff(c_60, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_57])).
% 1.90/1.24  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_60])).
% 1.90/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.24  
% 1.90/1.24  Inference rules
% 1.90/1.24  ----------------------
% 1.90/1.24  #Ref     : 0
% 1.90/1.24  #Sup     : 9
% 1.90/1.24  #Fact    : 0
% 1.90/1.24  #Define  : 0
% 1.90/1.24  #Split   : 0
% 1.90/1.24  #Chain   : 0
% 1.90/1.24  #Close   : 0
% 1.90/1.24  
% 1.90/1.24  Ordering : KBO
% 1.90/1.24  
% 1.90/1.24  Simplification rules
% 1.90/1.24  ----------------------
% 1.90/1.24  #Subsume      : 0
% 1.90/1.24  #Demod        : 4
% 1.90/1.24  #Tautology    : 6
% 1.90/1.24  #SimpNegUnit  : 1
% 1.90/1.24  #BackRed      : 0
% 1.90/1.24  
% 1.90/1.24  #Partial instantiations: 0
% 1.90/1.24  #Strategies tried      : 1
% 1.90/1.24  
% 1.90/1.24  Timing (in seconds)
% 1.90/1.24  ----------------------
% 1.90/1.24  Preprocessing        : 0.33
% 1.90/1.24  Parsing              : 0.17
% 1.90/1.24  CNF conversion       : 0.02
% 1.90/1.24  Main loop            : 0.09
% 1.90/1.24  Inferencing          : 0.04
% 1.90/1.24  Reduction            : 0.03
% 1.90/1.24  Demodulation         : 0.02
% 1.90/1.24  BG Simplification    : 0.01
% 1.90/1.24  Subsumption          : 0.01
% 1.90/1.24  Abstraction          : 0.01
% 1.90/1.24  MUC search           : 0.00
% 1.90/1.24  Cooper               : 0.00
% 1.90/1.24  Total                : 0.45
% 1.90/1.24  Index Insertion      : 0.00
% 1.90/1.24  Index Deletion       : 0.00
% 1.90/1.24  Index Matching       : 0.00
% 1.90/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
