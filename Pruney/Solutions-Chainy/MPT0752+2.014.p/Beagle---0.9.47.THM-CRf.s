%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_16,plain,(
    ! [A_5] :
      ( v5_ordinal1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_27,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_12,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_8,plain,(
    ! [B_3] : v5_relat_1(k1_xboole_0,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_35,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_25,c_20])).

tff(c_39,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_35])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_39])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  %$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.10  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.62/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.62/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.10  
% 1.62/1.11  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.62/1.11  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.62/1.11  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.62/1.11  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.62/1.11  tff(f_40, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.62/1.11  tff(f_35, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.62/1.11  tff(f_53, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.62/1.11  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.11  tff(c_40, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.11  tff(c_44, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.62/1.11  tff(c_16, plain, (![A_5]: (v5_ordinal1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.11  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.11  tff(c_14, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.11  tff(c_27, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_14])).
% 1.62/1.11  tff(c_12, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.11  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_12])).
% 1.62/1.11  tff(c_8, plain, (![B_3]: (v5_relat_1(k1_xboole_0, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.11  tff(c_18, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_2') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.62/1.11  tff(c_20, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 1.62/1.11  tff(c_35, plain, (~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27, c_25, c_20])).
% 1.62/1.11  tff(c_39, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_35])).
% 1.62/1.11  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_39])).
% 1.62/1.11  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 1.62/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  Inference rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Ref     : 0
% 1.62/1.11  #Sup     : 6
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 0
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 13
% 1.62/1.11  #Tautology    : 2
% 1.62/1.11  #SimpNegUnit  : 0
% 1.62/1.11  #BackRed      : 8
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.12  Preprocessing        : 0.25
% 1.62/1.12  Parsing              : 0.14
% 1.62/1.12  CNF conversion       : 0.01
% 1.62/1.12  Main loop            : 0.09
% 1.62/1.12  Inferencing          : 0.04
% 1.62/1.12  Reduction            : 0.03
% 1.62/1.12  Demodulation         : 0.02
% 1.62/1.12  BG Simplification    : 0.01
% 1.62/1.12  Subsumption          : 0.01
% 1.62/1.12  Abstraction          : 0.00
% 1.62/1.12  MUC search           : 0.00
% 1.62/1.12  Cooper               : 0.00
% 1.62/1.12  Total                : 0.36
% 1.62/1.12  Index Insertion      : 0.00
% 1.62/1.12  Index Deletion       : 0.00
% 1.62/1.12  Index Matching       : 0.00
% 1.62/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
