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
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v3_ordinal1 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

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

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_55,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v1_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_wellord2)).

tff(f_49,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v6_relat_2(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_43,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

tff(f_51,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_45,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(c_28,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_7] :
      ( v1_wellord1(k1_wellord2(A_7))
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_5] :
      ( v6_relat_2(k1_wellord2(A_5))
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_2] : v1_relat_1(k1_wellord2(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_3] : v1_relat_2(k1_wellord2(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_6] : v4_relat_2(k1_wellord2(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_4] : v8_relat_2(k1_wellord2(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_19] :
      ( v2_wellord1(A_19)
      | ~ v1_wellord1(A_19)
      | ~ v6_relat_2(A_19)
      | ~ v4_relat_2(A_19)
      | ~ v8_relat_2(A_19)
      | ~ v1_relat_2(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_4] :
      ( v2_wellord1(k1_wellord2(A_4))
      | ~ v1_wellord1(k1_wellord2(A_4))
      | ~ v6_relat_2(k1_wellord2(A_4))
      | ~ v4_relat_2(k1_wellord2(A_4))
      | ~ v1_relat_2(k1_wellord2(A_4))
      | ~ v1_relat_1(k1_wellord2(A_4)) ) ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_51,plain,(
    ! [A_20] :
      ( v2_wellord1(k1_wellord2(A_20))
      | ~ v1_wellord1(k1_wellord2(A_20))
      | ~ v6_relat_2(k1_wellord2(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_22,c_46])).

tff(c_62,plain,(
    ! [A_21] :
      ( v2_wellord1(k1_wellord2(A_21))
      | ~ v1_wellord1(k1_wellord2(A_21))
      | ~ v3_ordinal1(A_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_26,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,
    ( ~ v1_wellord1(k1_wellord2('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_26])).

tff(c_80,plain,(
    ~ v1_wellord1(k1_wellord2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_83,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  %$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v3_ordinal1 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_1
% 1.65/1.13  
% 1.65/1.13  %Foreground sorts:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Background operators:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Foreground operators:
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.13  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.65/1.13  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 1.65/1.13  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 1.65/1.13  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 1.65/1.13  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.65/1.13  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.65/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.13  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.13  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 1.65/1.13  
% 1.65/1.14  tff(f_60, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 1.65/1.14  tff(f_55, axiom, (![A]: (v3_ordinal1(A) => v1_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_wellord2)).
% 1.65/1.14  tff(f_49, axiom, (![A]: (v3_ordinal1(A) => v6_relat_2(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_wellord2)).
% 1.65/1.14  tff(f_41, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.65/1.14  tff(f_43, axiom, (![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 1.65/1.14  tff(f_51, axiom, (![A]: v4_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord2)).
% 1.65/1.14  tff(f_45, axiom, (![A]: v8_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 1.65/1.14  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 1.65/1.14  tff(c_28, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.14  tff(c_24, plain, (![A_7]: (v1_wellord1(k1_wellord2(A_7)) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.14  tff(c_20, plain, (![A_5]: (v6_relat_2(k1_wellord2(A_5)) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.14  tff(c_14, plain, (![A_2]: (v1_relat_1(k1_wellord2(A_2)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.14  tff(c_16, plain, (![A_3]: (v1_relat_2(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.14  tff(c_22, plain, (![A_6]: (v4_relat_2(k1_wellord2(A_6)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.14  tff(c_18, plain, (![A_4]: (v8_relat_2(k1_wellord2(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.14  tff(c_40, plain, (![A_19]: (v2_wellord1(A_19) | ~v1_wellord1(A_19) | ~v6_relat_2(A_19) | ~v4_relat_2(A_19) | ~v8_relat_2(A_19) | ~v1_relat_2(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.14  tff(c_46, plain, (![A_4]: (v2_wellord1(k1_wellord2(A_4)) | ~v1_wellord1(k1_wellord2(A_4)) | ~v6_relat_2(k1_wellord2(A_4)) | ~v4_relat_2(k1_wellord2(A_4)) | ~v1_relat_2(k1_wellord2(A_4)) | ~v1_relat_1(k1_wellord2(A_4)))), inference(resolution, [status(thm)], [c_18, c_40])).
% 1.65/1.14  tff(c_51, plain, (![A_20]: (v2_wellord1(k1_wellord2(A_20)) | ~v1_wellord1(k1_wellord2(A_20)) | ~v6_relat_2(k1_wellord2(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_22, c_46])).
% 1.65/1.14  tff(c_62, plain, (![A_21]: (v2_wellord1(k1_wellord2(A_21)) | ~v1_wellord1(k1_wellord2(A_21)) | ~v3_ordinal1(A_21))), inference(resolution, [status(thm)], [c_20, c_51])).
% 1.65/1.14  tff(c_26, plain, (~v2_wellord1(k1_wellord2('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.14  tff(c_71, plain, (~v1_wellord1(k1_wellord2('#skF_1')) | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_62, c_26])).
% 1.65/1.14  tff(c_80, plain, (~v1_wellord1(k1_wellord2('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71])).
% 1.65/1.14  tff(c_83, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_80])).
% 1.65/1.14  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_83])).
% 1.65/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  Inference rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Ref     : 0
% 1.65/1.14  #Sup     : 8
% 1.65/1.14  #Fact    : 0
% 1.65/1.14  #Define  : 0
% 1.65/1.14  #Split   : 0
% 1.65/1.14  #Chain   : 0
% 1.65/1.14  #Close   : 0
% 1.65/1.14  
% 1.65/1.14  Ordering : KBO
% 1.65/1.14  
% 1.65/1.14  Simplification rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Subsume      : 1
% 1.65/1.14  #Demod        : 9
% 1.65/1.14  #Tautology    : 3
% 1.65/1.14  #SimpNegUnit  : 0
% 1.65/1.14  #BackRed      : 0
% 1.65/1.14  
% 1.65/1.14  #Partial instantiations: 0
% 1.65/1.14  #Strategies tried      : 1
% 1.65/1.14  
% 1.65/1.14  Timing (in seconds)
% 1.65/1.14  ----------------------
% 1.65/1.15  Preprocessing        : 0.26
% 1.65/1.15  Parsing              : 0.15
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.12
% 1.65/1.15  Inferencing          : 0.06
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.03
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.02
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.41
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
