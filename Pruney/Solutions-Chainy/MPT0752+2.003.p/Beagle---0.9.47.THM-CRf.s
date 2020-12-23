%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  46 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : v1_xboole_0(k1_subset_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    ! [A_7] :
      ( v5_ordinal1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [A_13] :
      ( v1_funct_1(A_13)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19,c_35])).

tff(c_29,plain,(
    ! [A_11] :
      ( v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19,c_29])).

tff(c_10,plain,(
    ! [B_5] : v5_relat_1(k1_xboole_0,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_41,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_33,c_18])).

tff(c_44,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  %$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.60/1.10  
% 1.60/1.10  %Foreground sorts:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Background operators:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Foreground operators:
% 1.60/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.10  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.60/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.10  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.60/1.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.60/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.10  
% 1.60/1.11  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.60/1.11  tff(f_29, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.60/1.11  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.60/1.11  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.60/1.11  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.60/1.11  tff(f_37, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 1.60/1.11  tff(f_54, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.60/1.11  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.11  tff(c_4, plain, (![A_2]: (v1_xboole_0(k1_subset_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.11  tff(c_19, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.60/1.11  tff(c_14, plain, (![A_7]: (v5_ordinal1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.11  tff(c_35, plain, (![A_13]: (v1_funct_1(A_13) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.11  tff(c_39, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_19, c_35])).
% 1.60/1.11  tff(c_29, plain, (![A_11]: (v1_relat_1(A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.11  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_19, c_29])).
% 1.60/1.11  tff(c_10, plain, (![B_5]: (v5_relat_1(k1_xboole_0, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.11  tff(c_16, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.11  tff(c_18, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.60/1.11  tff(c_41, plain, (~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_33, c_18])).
% 1.60/1.11  tff(c_44, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_41])).
% 1.60/1.11  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19, c_44])).
% 1.60/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  Inference rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Ref     : 0
% 1.60/1.11  #Sup     : 5
% 1.60/1.11  #Fact    : 0
% 1.60/1.11  #Define  : 0
% 1.60/1.11  #Split   : 0
% 1.60/1.11  #Chain   : 0
% 1.60/1.11  #Close   : 0
% 1.60/1.11  
% 1.60/1.11  Ordering : KBO
% 1.60/1.11  
% 1.60/1.11  Simplification rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Subsume      : 0
% 1.60/1.11  #Demod        : 5
% 1.60/1.11  #Tautology    : 2
% 1.60/1.11  #SimpNegUnit  : 0
% 1.60/1.11  #BackRed      : 0
% 1.60/1.11  
% 1.60/1.11  #Partial instantiations: 0
% 1.60/1.11  #Strategies tried      : 1
% 1.60/1.11  
% 1.60/1.11  Timing (in seconds)
% 1.60/1.11  ----------------------
% 1.60/1.11  Preprocessing        : 0.24
% 1.60/1.11  Parsing              : 0.14
% 1.60/1.11  CNF conversion       : 0.01
% 1.60/1.11  Main loop            : 0.08
% 1.60/1.11  Inferencing          : 0.04
% 1.60/1.11  Reduction            : 0.02
% 1.60/1.11  Demodulation         : 0.02
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.00
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.35
% 1.60/1.11  Index Insertion      : 0.00
% 1.60/1.11  Index Deletion       : 0.00
% 1.60/1.11  Index Matching       : 0.00
% 1.60/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
