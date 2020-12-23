%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:26 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  82 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_30,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_30])).

tff(c_35,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_33])).

tff(c_20,plain,(
    ! [B_5,A_6] :
      ( ~ v1_xboole_0(B_5)
      | B_5 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_23,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_35,c_23])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_38])).

tff(c_45,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_62,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_62])).

tff(c_67,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_65])).

tff(c_51,plain,(
    ! [B_9,A_10] :
      ( ~ v1_xboole_0(B_9)
      | B_9 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_67,c_54])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:32:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.10  
% 1.62/1.11  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.62/1.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.62/1.11  tff(f_42, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.62/1.11  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.62/1.11  tff(f_50, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.62/1.11  tff(c_10, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.62/1.11  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.62/1.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.62/1.11  tff(c_12, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.62/1.11  tff(c_15, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 1.62/1.11  tff(c_30, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.11  tff(c_33, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15, c_30])).
% 1.62/1.11  tff(c_35, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_33])).
% 1.62/1.11  tff(c_20, plain, (![B_5, A_6]: (~v1_xboole_0(B_5) | B_5=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.11  tff(c_23, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2, c_20])).
% 1.62/1.11  tff(c_38, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_35, c_23])).
% 1.62/1.11  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_38])).
% 1.62/1.11  tff(c_45, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.62/1.11  tff(c_62, plain, (![A_13]: (~v1_xboole_0(k2_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.11  tff(c_65, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_62])).
% 1.62/1.11  tff(c_67, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_65])).
% 1.62/1.11  tff(c_51, plain, (![B_9, A_10]: (~v1_xboole_0(B_9) | B_9=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.11  tff(c_54, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.62/1.11  tff(c_70, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_67, c_54])).
% 1.62/1.11  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_70])).
% 1.62/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  Inference rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Ref     : 0
% 1.62/1.11  #Sup     : 14
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 1
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 4
% 1.62/1.11  #Tautology    : 6
% 1.62/1.11  #SimpNegUnit  : 2
% 1.62/1.11  #BackRed      : 0
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.12  Preprocessing        : 0.26
% 1.62/1.12  Parsing              : 0.14
% 1.62/1.12  CNF conversion       : 0.01
% 1.62/1.12  Main loop            : 0.09
% 1.62/1.12  Inferencing          : 0.04
% 1.62/1.12  Reduction            : 0.02
% 1.62/1.12  Demodulation         : 0.02
% 1.62/1.12  BG Simplification    : 0.01
% 1.62/1.12  Subsumption          : 0.01
% 1.62/1.12  Abstraction          : 0.00
% 1.62/1.12  MUC search           : 0.00
% 1.62/1.12  Cooper               : 0.00
% 1.62/1.12  Total                : 0.38
% 1.62/1.12  Index Insertion      : 0.00
% 1.62/1.12  Index Deletion       : 0.00
% 1.62/1.12  Index Matching       : 0.00
% 1.62/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
