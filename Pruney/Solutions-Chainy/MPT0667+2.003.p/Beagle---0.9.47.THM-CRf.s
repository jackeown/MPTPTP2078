%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:18 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  63 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => v2_funct_1(k7_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_relat_1(A_1),B_2) = k7_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_13,B_14] :
      ( v2_funct_1(k5_relat_1(A_13,B_14))
      | ~ v2_funct_1(B_14)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_37,plain,(
    ! [B_2,A_1] :
      ( v2_funct_1(k7_relat_1(B_2,A_1))
      | ~ v2_funct_1(B_2)
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_40,plain,(
    ! [B_15,A_16] :
      ( v2_funct_1(k7_relat_1(B_15,A_16))
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_10,c_37])).

tff(c_14,plain,(
    ~ v2_funct_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.08  
% 1.63/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.63/1.09  
% 1.63/1.09  %Foreground sorts:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Background operators:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Foreground operators:
% 1.63/1.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.63/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.63/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  
% 1.63/1.09  tff(f_61, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => v2_funct_1(k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_funct_1)).
% 1.63/1.09  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.63/1.09  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.63/1.09  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.63/1.09  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_1)).
% 1.63/1.09  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.63/1.09  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.63/1.09  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.63/1.09  tff(c_8, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.09  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.09  tff(c_10, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.09  tff(c_2, plain, (![A_1, B_2]: (k5_relat_1(k6_relat_1(A_1), B_2)=k7_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_34, plain, (![A_13, B_14]: (v2_funct_1(k5_relat_1(A_13, B_14)) | ~v2_funct_1(B_14) | ~v2_funct_1(A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.63/1.09  tff(c_37, plain, (![B_2, A_1]: (v2_funct_1(k7_relat_1(B_2, A_1)) | ~v2_funct_1(B_2) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_34])).
% 1.63/1.09  tff(c_40, plain, (![B_15, A_16]: (v2_funct_1(k7_relat_1(B_15, A_16)) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_10, c_37])).
% 1.63/1.09  tff(c_14, plain, (~v2_funct_1(k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.63/1.09  tff(c_43, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_14])).
% 1.63/1.09  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_43])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 4
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 0
% 1.63/1.09  #Chain   : 0
% 1.63/1.09  #Close   : 0
% 1.63/1.09  
% 1.63/1.09  Ordering : KBO
% 1.63/1.09  
% 1.63/1.09  Simplification rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Subsume      : 0
% 1.63/1.09  #Demod        : 7
% 1.63/1.09  #Tautology    : 3
% 1.63/1.09  #SimpNegUnit  : 0
% 1.63/1.09  #BackRed      : 0
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.10  Preprocessing        : 0.24
% 1.63/1.10  Parsing              : 0.13
% 1.63/1.10  CNF conversion       : 0.01
% 1.63/1.10  Main loop            : 0.08
% 1.63/1.10  Inferencing          : 0.03
% 1.63/1.10  Reduction            : 0.02
% 1.63/1.10  Demodulation         : 0.02
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.01
% 1.63/1.10  Abstraction          : 0.00
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.36
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
