%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:18 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 (  64 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => v2_funct_1(k7_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

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

tff(c_42,plain,(
    ! [A_14,B_15] :
      ( v2_funct_1(k5_relat_1(A_14,B_15))
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [B_2,A_1] :
      ( v2_funct_1(k7_relat_1(B_2,A_1))
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_49,plain,(
    ! [B_18,A_19] :
      ( v2_funct_1(k7_relat_1(B_18,A_19))
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_10,c_45])).

tff(c_16,plain,(
    ~ v2_funct_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_16])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.10  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.58/1.10  
% 1.58/1.10  %Foreground sorts:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Background operators:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Foreground operators:
% 1.58/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.58/1.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.58/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.58/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.10  
% 1.58/1.11  tff(f_62, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => v2_funct_1(k7_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_funct_1)).
% 1.58/1.11  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.58/1.11  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.58/1.11  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.58/1.11  tff(f_53, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 1.58/1.11  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.58/1.11  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.58/1.11  tff(c_18, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.58/1.11  tff(c_8, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.58/1.11  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.11  tff(c_10, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.58/1.11  tff(c_2, plain, (![A_1, B_2]: (k5_relat_1(k6_relat_1(A_1), B_2)=k7_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.11  tff(c_42, plain, (![A_14, B_15]: (v2_funct_1(k5_relat_1(A_14, B_15)) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.58/1.11  tff(c_45, plain, (![B_2, A_1]: (v2_funct_1(k7_relat_1(B_2, A_1)) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_42])).
% 1.58/1.11  tff(c_49, plain, (![B_18, A_19]: (v2_funct_1(k7_relat_1(B_18, A_19)) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_10, c_45])).
% 1.58/1.11  tff(c_16, plain, (~v2_funct_1(k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.58/1.11  tff(c_52, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_49, c_16])).
% 1.58/1.11  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_52])).
% 1.58/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.11  
% 1.58/1.11  Inference rules
% 1.58/1.11  ----------------------
% 1.58/1.11  #Ref     : 0
% 1.58/1.11  #Sup     : 5
% 1.58/1.11  #Fact    : 0
% 1.58/1.11  #Define  : 0
% 1.58/1.11  #Split   : 0
% 1.58/1.11  #Chain   : 0
% 1.58/1.11  #Close   : 0
% 1.58/1.11  
% 1.58/1.11  Ordering : KBO
% 1.58/1.11  
% 1.58/1.11  Simplification rules
% 1.58/1.11  ----------------------
% 1.58/1.11  #Subsume      : 0
% 1.58/1.11  #Demod        : 10
% 1.58/1.11  #Tautology    : 3
% 1.58/1.11  #SimpNegUnit  : 0
% 1.58/1.11  #BackRed      : 0
% 1.58/1.11  
% 1.58/1.11  #Partial instantiations: 0
% 1.58/1.11  #Strategies tried      : 1
% 1.58/1.11  
% 1.58/1.11  Timing (in seconds)
% 1.58/1.11  ----------------------
% 1.58/1.12  Preprocessing        : 0.25
% 1.58/1.12  Parsing              : 0.14
% 1.58/1.12  CNF conversion       : 0.02
% 1.58/1.12  Main loop            : 0.10
% 1.58/1.12  Inferencing          : 0.04
% 1.58/1.12  Reduction            : 0.03
% 1.58/1.12  Demodulation         : 0.02
% 1.58/1.12  BG Simplification    : 0.01
% 1.58/1.12  Subsumption          : 0.01
% 1.58/1.12  Abstraction          : 0.00
% 1.58/1.12  MUC search           : 0.00
% 1.58/1.12  Cooper               : 0.00
% 1.58/1.12  Total                : 0.38
% 1.58/1.12  Index Insertion      : 0.00
% 1.58/1.12  Index Deletion       : 0.00
% 1.58/1.12  Index Matching       : 0.00
% 1.58/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
