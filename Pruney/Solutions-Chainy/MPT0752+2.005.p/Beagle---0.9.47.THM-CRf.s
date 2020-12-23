%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_xboole_0 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_5] :
      ( v5_ordinal1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19,plain,(
    ! [A_8] :
      ( v1_funct_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_23,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

tff(c_25,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

tff(c_8,plain,(
    ! [B_3] : v5_relat_1(k1_xboole_0,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_31,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_29,c_16])).

tff(c_34,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:57:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.59/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  %$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.59/1.15  
% 1.59/1.15  %Foreground sorts:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Background operators:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Foreground operators:
% 1.59/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.15  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.59/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.59/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.15  
% 1.59/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.59/1.16  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.59/1.16  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.59/1.16  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.59/1.16  tff(f_34, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.59/1.16  tff(f_51, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.59/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.59/1.16  tff(c_12, plain, (![A_5]: (v5_ordinal1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.16  tff(c_19, plain, (![A_8]: (v1_funct_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.16  tff(c_23, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_19])).
% 1.59/1.16  tff(c_25, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.59/1.16  tff(c_29, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_25])).
% 1.59/1.16  tff(c_8, plain, (![B_3]: (v5_relat_1(k1_xboole_0, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.16  tff(c_14, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.59/1.16  tff(c_16, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.59/1.16  tff(c_31, plain, (~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23, c_29, c_16])).
% 1.59/1.16  tff(c_34, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_31])).
% 1.59/1.16  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 1.59/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  Inference rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Ref     : 0
% 1.59/1.16  #Sup     : 3
% 1.59/1.16  #Fact    : 0
% 1.59/1.16  #Define  : 0
% 1.59/1.16  #Split   : 0
% 1.59/1.16  #Chain   : 0
% 1.59/1.16  #Close   : 0
% 1.59/1.16  
% 1.59/1.16  Ordering : KBO
% 1.59/1.16  
% 1.59/1.16  Simplification rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Subsume      : 0
% 1.59/1.16  #Demod        : 4
% 1.59/1.16  #Tautology    : 0
% 1.59/1.16  #SimpNegUnit  : 0
% 1.59/1.16  #BackRed      : 0
% 1.59/1.16  
% 1.59/1.16  #Partial instantiations: 0
% 1.59/1.16  #Strategies tried      : 1
% 1.59/1.16  
% 1.59/1.16  Timing (in seconds)
% 1.59/1.16  ----------------------
% 1.59/1.16  Preprocessing        : 0.27
% 1.59/1.16  Parsing              : 0.15
% 1.59/1.16  CNF conversion       : 0.02
% 1.59/1.16  Main loop            : 0.07
% 1.59/1.16  Inferencing          : 0.04
% 1.59/1.16  Reduction            : 0.02
% 1.59/1.16  Demodulation         : 0.02
% 1.59/1.16  BG Simplification    : 0.01
% 1.59/1.16  Subsumption          : 0.01
% 1.59/1.16  Abstraction          : 0.00
% 1.59/1.16  MUC search           : 0.00
% 1.59/1.17  Cooper               : 0.00
% 1.59/1.17  Total                : 0.37
% 1.59/1.17  Index Insertion      : 0.00
% 1.59/1.17  Index Deletion       : 0.00
% 1.59/1.17  Index Matching       : 0.00
% 1.59/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
