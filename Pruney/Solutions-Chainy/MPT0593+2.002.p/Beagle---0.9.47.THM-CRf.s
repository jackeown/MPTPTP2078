%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:10 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  72 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( k2_relat_1(A) = k1_xboole_0
                & k2_relat_1(B) = k1_xboole_0 )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_14,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_41])).

tff(c_49,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_19,c_44])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_41])).

tff(c_51,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_19,c_47])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_70,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_59])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.09  
% 1.57/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.09  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.57/1.09  
% 1.57/1.09  %Foreground sorts:
% 1.57/1.09  
% 1.57/1.09  
% 1.57/1.09  %Background operators:
% 1.57/1.09  
% 1.57/1.09  
% 1.57/1.09  %Foreground operators:
% 1.57/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.57/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.09  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.57/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.57/1.09  
% 1.57/1.10  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t197_relat_1)).
% 1.57/1.10  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.57/1.10  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.57/1.10  tff(f_41, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.57/1.10  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.57/1.10  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.10  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.10  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.10  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.10  tff(c_19, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.57/1.10  tff(c_14, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.10  tff(c_41, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.57/1.10  tff(c_44, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_41])).
% 1.57/1.10  tff(c_49, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_19, c_44])).
% 1.57/1.10  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.10  tff(c_55, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_49, c_2])).
% 1.57/1.10  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.10  tff(c_12, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.10  tff(c_47, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_41])).
% 1.57/1.10  tff(c_51, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_19, c_47])).
% 1.57/1.10  tff(c_59, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_51, c_2])).
% 1.57/1.10  tff(c_70, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_59])).
% 1.57/1.10  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_70])).
% 1.57/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.10  
% 1.57/1.10  Inference rules
% 1.57/1.10  ----------------------
% 1.57/1.10  #Ref     : 0
% 1.57/1.10  #Sup     : 13
% 1.57/1.10  #Fact    : 0
% 1.57/1.10  #Define  : 0
% 1.57/1.10  #Split   : 0
% 1.57/1.10  #Chain   : 0
% 1.57/1.10  #Close   : 0
% 1.57/1.10  
% 1.57/1.10  Ordering : KBO
% 1.57/1.10  
% 1.57/1.10  Simplification rules
% 1.57/1.10  ----------------------
% 1.57/1.10  #Subsume      : 0
% 1.57/1.10  #Demod        : 12
% 1.57/1.10  #Tautology    : 10
% 1.57/1.10  #SimpNegUnit  : 1
% 1.57/1.10  #BackRed      : 5
% 1.57/1.10  
% 1.57/1.10  #Partial instantiations: 0
% 1.57/1.10  #Strategies tried      : 1
% 1.57/1.10  
% 1.57/1.10  Timing (in seconds)
% 1.57/1.10  ----------------------
% 1.57/1.10  Preprocessing        : 0.26
% 1.57/1.10  Parsing              : 0.14
% 1.57/1.10  CNF conversion       : 0.01
% 1.57/1.10  Main loop            : 0.09
% 1.57/1.10  Inferencing          : 0.03
% 1.57/1.10  Reduction            : 0.03
% 1.57/1.10  Demodulation         : 0.02
% 1.57/1.10  BG Simplification    : 0.01
% 1.57/1.10  Subsumption          : 0.01
% 1.57/1.10  Abstraction          : 0.00
% 1.57/1.10  MUC search           : 0.00
% 1.57/1.11  Cooper               : 0.00
% 1.57/1.11  Total                : 0.37
% 1.57/1.11  Index Insertion      : 0.00
% 1.57/1.11  Index Deletion       : 0.00
% 1.57/1.11  Index Matching       : 0.00
% 1.57/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
