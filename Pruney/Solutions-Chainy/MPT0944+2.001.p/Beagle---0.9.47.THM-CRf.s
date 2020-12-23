%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( r1_tarski(B,A)
           => v2_wellord1(k1_wellord2(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

tff(c_10,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_4] :
      ( v2_wellord1(k1_wellord2(A_4))
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k1_wellord2(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [B_12,A_13] :
      ( k2_wellord1(k1_wellord2(B_12),A_13) = k1_wellord2(A_13)
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v2_wellord1(k2_wellord1(B_2,A_1))
      | ~ v2_wellord1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_13,B_12] :
      ( v2_wellord1(k1_wellord2(A_13))
      | ~ v2_wellord1(k1_wellord2(B_12))
      | ~ v1_relat_1(k1_wellord2(B_12))
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( v2_wellord1(k1_wellord2(A_14))
      | ~ v2_wellord1(k1_wellord2(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_40,plain,(
    ! [A_16,A_17] :
      ( v2_wellord1(k1_wellord2(A_16))
      | ~ r1_tarski(A_16,A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_42,plain,
    ( v2_wellord1(k1_wellord2('#skF_2'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_45,plain,(
    v2_wellord1(k1_wellord2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.37  
% 1.94/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.38  %$ r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_2 > #skF_1
% 1.94/1.38  
% 1.94/1.38  %Foreground sorts:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Background operators:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Foreground operators:
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.38  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.94/1.38  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.94/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.94/1.38  
% 2.04/1.39  tff(f_49, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (r1_tarski(B, A) => v2_wellord1(k1_wellord2(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_wellord2)).
% 2.04/1.39  tff(f_37, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.04/1.39  tff(f_33, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.04/1.39  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.04/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => v2_wellord1(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord1)).
% 2.04/1.39  tff(c_10, plain, (~v2_wellord1(k1_wellord2('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.39  tff(c_14, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.39  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.39  tff(c_6, plain, (![A_4]: (v2_wellord1(k1_wellord2(A_4)) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.39  tff(c_4, plain, (![A_3]: (v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.39  tff(c_22, plain, (![B_12, A_13]: (k2_wellord1(k1_wellord2(B_12), A_13)=k1_wellord2(A_13) | ~r1_tarski(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.39  tff(c_2, plain, (![B_2, A_1]: (v2_wellord1(k2_wellord1(B_2, A_1)) | ~v2_wellord1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.39  tff(c_28, plain, (![A_13, B_12]: (v2_wellord1(k1_wellord2(A_13)) | ~v2_wellord1(k1_wellord2(B_12)) | ~v1_relat_1(k1_wellord2(B_12)) | ~r1_tarski(A_13, B_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2])).
% 2.04/1.39  tff(c_36, plain, (![A_14, B_15]: (v2_wellord1(k1_wellord2(A_14)) | ~v2_wellord1(k1_wellord2(B_15)) | ~r1_tarski(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 2.04/1.39  tff(c_40, plain, (![A_16, A_17]: (v2_wellord1(k1_wellord2(A_16)) | ~r1_tarski(A_16, A_17) | ~v3_ordinal1(A_17))), inference(resolution, [status(thm)], [c_6, c_36])).
% 2.04/1.39  tff(c_42, plain, (v2_wellord1(k1_wellord2('#skF_2')) | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.04/1.39  tff(c_45, plain, (v2_wellord1(k1_wellord2('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42])).
% 2.04/1.39  tff(c_47, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_45])).
% 2.04/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.39  
% 2.04/1.39  Inference rules
% 2.04/1.39  ----------------------
% 2.04/1.39  #Ref     : 0
% 2.04/1.39  #Sup     : 6
% 2.04/1.39  #Fact    : 0
% 2.04/1.39  #Define  : 0
% 2.04/1.39  #Split   : 0
% 2.04/1.39  #Chain   : 0
% 2.04/1.39  #Close   : 0
% 2.04/1.39  
% 2.04/1.39  Ordering : KBO
% 2.04/1.39  
% 2.04/1.39  Simplification rules
% 2.04/1.39  ----------------------
% 2.04/1.39  #Subsume      : 0
% 2.04/1.39  #Demod        : 2
% 2.04/1.39  #Tautology    : 2
% 2.04/1.39  #SimpNegUnit  : 1
% 2.04/1.39  #BackRed      : 0
% 2.04/1.39  
% 2.04/1.39  #Partial instantiations: 0
% 2.04/1.39  #Strategies tried      : 1
% 2.04/1.39  
% 2.04/1.39  Timing (in seconds)
% 2.04/1.39  ----------------------
% 2.04/1.40  Preprocessing        : 0.40
% 2.04/1.40  Parsing              : 0.22
% 2.04/1.40  CNF conversion       : 0.02
% 2.04/1.40  Main loop            : 0.16
% 2.04/1.40  Inferencing          : 0.07
% 2.04/1.40  Reduction            : 0.04
% 2.04/1.40  Demodulation         : 0.03
% 2.04/1.40  BG Simplification    : 0.01
% 2.04/1.40  Subsumption          : 0.02
% 2.04/1.40  Abstraction          : 0.01
% 2.04/1.40  MUC search           : 0.00
% 2.04/1.40  Cooper               : 0.00
% 2.04/1.40  Total                : 0.59
% 2.04/1.40  Index Insertion      : 0.00
% 2.04/1.40  Index Deletion       : 0.00
% 2.04/1.40  Index Matching       : 0.00
% 2.04/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
