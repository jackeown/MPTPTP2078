%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
         => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_5,B_6] :
      ( v1_finset_1(k9_relat_1(A_5,B_6))
      | ~ v1_finset_1(B_6)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_7] :
      ( v1_finset_1(k2_relat_1(A_7))
      | ~ v1_finset_1(k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_6,plain,(
    ~ v1_finset_1(k2_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,
    ( ~ v1_finset_1(k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_6])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_8,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:02:16 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.05  
% 1.52/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.05  %$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.52/1.05  
% 1.52/1.05  %Foreground sorts:
% 1.52/1.05  
% 1.52/1.05  
% 1.52/1.05  %Background operators:
% 1.52/1.05  
% 1.52/1.05  
% 1.52/1.05  %Foreground operators:
% 1.52/1.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.52/1.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.52/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.05  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.52/1.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.52/1.05  
% 1.52/1.06  tff(f_46, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) => v1_finset_1(k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 1.52/1.06  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.52/1.06  tff(f_37, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 1.52/1.06  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.52/1.06  tff(c_10, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.52/1.06  tff(c_8, plain, (v1_finset_1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.52/1.06  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.06  tff(c_22, plain, (![A_5, B_6]: (v1_finset_1(k9_relat_1(A_5, B_6)) | ~v1_finset_1(B_6) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.52/1.06  tff(c_26, plain, (![A_7]: (v1_finset_1(k2_relat_1(A_7)) | ~v1_finset_1(k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22])).
% 1.52/1.06  tff(c_6, plain, (~v1_finset_1(k2_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.52/1.06  tff(c_29, plain, (~v1_finset_1(k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_6])).
% 1.52/1.06  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_8, c_29])).
% 1.52/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  Inference rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Ref     : 0
% 1.52/1.06  #Sup     : 4
% 1.52/1.06  #Fact    : 0
% 1.52/1.06  #Define  : 0
% 1.52/1.06  #Split   : 0
% 1.52/1.06  #Chain   : 0
% 1.52/1.06  #Close   : 0
% 1.52/1.06  
% 1.52/1.06  Ordering : KBO
% 1.52/1.06  
% 1.52/1.06  Simplification rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Subsume      : 0
% 1.52/1.06  #Demod        : 3
% 1.52/1.06  #Tautology    : 2
% 1.52/1.06  #SimpNegUnit  : 0
% 1.52/1.06  #BackRed      : 0
% 1.52/1.06  
% 1.52/1.06  #Partial instantiations: 0
% 1.52/1.06  #Strategies tried      : 1
% 1.52/1.06  
% 1.52/1.06  Timing (in seconds)
% 1.52/1.06  ----------------------
% 1.52/1.06  Preprocessing        : 0.25
% 1.52/1.06  Parsing              : 0.14
% 1.52/1.06  CNF conversion       : 0.01
% 1.52/1.06  Main loop            : 0.08
% 1.52/1.06  Inferencing          : 0.04
% 1.52/1.06  Reduction            : 0.02
% 1.52/1.06  Demodulation         : 0.01
% 1.52/1.06  BG Simplification    : 0.01
% 1.52/1.06  Subsumption          : 0.00
% 1.52/1.06  Abstraction          : 0.00
% 1.52/1.06  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.35
% 1.52/1.07  Index Insertion      : 0.00
% 1.52/1.07  Index Deletion       : 0.00
% 1.52/1.07  Index Matching       : 0.00
% 1.52/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
