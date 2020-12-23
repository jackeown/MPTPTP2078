%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:10 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 100 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_57,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_18,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    ! [A_10] :
      ( k8_relat_1(k2_relat_1(A_10),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,
    ( k8_relat_1(k1_xboole_0,'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_45])).

tff(c_61,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_86,plain,(
    ! [B_13,A_14] :
      ( v1_xboole_0(k8_relat_1(B_13,A_14))
      | ~ v1_xboole_0(B_13)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_86])).

tff(c_103,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_23,c_95])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,
    ( k8_relat_1(k1_xboole_0,'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_45])).

tff(c_63,plain,(
    k8_relat_1(k1_xboole_0,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_57])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_86])).

tff(c_101,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23,c_92])).

tff(c_107,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_138,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_107])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.23  %$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.83/1.23  
% 1.83/1.23  %Foreground sorts:
% 1.83/1.23  
% 1.83/1.23  
% 1.83/1.23  %Background operators:
% 1.83/1.23  
% 1.83/1.23  
% 1.83/1.23  %Foreground operators:
% 1.83/1.23  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.23  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.83/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.23  
% 1.94/1.24  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t197_relat_1)).
% 1.94/1.24  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.94/1.24  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.94/1.24  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 1.94/1.24  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc18_relat_1)).
% 1.94/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.24  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.24  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.24  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.24  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.24  tff(c_23, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.94/1.24  tff(c_18, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.24  tff(c_45, plain, (![A_10]: (k8_relat_1(k2_relat_1(A_10), A_10)=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.24  tff(c_54, plain, (k8_relat_1(k1_xboole_0, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_45])).
% 1.94/1.24  tff(c_61, plain, (k8_relat_1(k1_xboole_0, '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_54])).
% 1.94/1.24  tff(c_86, plain, (![B_13, A_14]: (v1_xboole_0(k8_relat_1(B_13, A_14)) | ~v1_xboole_0(B_13) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.24  tff(c_95, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_86])).
% 1.94/1.24  tff(c_103, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_23, c_95])).
% 1.94/1.24  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.24  tff(c_111, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_103, c_2])).
% 1.94/1.24  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.24  tff(c_16, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.24  tff(c_57, plain, (k8_relat_1(k1_xboole_0, '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_45])).
% 1.94/1.24  tff(c_63, plain, (k8_relat_1(k1_xboole_0, '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_57])).
% 1.94/1.24  tff(c_92, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_63, c_86])).
% 1.94/1.24  tff(c_101, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23, c_92])).
% 1.94/1.24  tff(c_107, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_101, c_2])).
% 1.94/1.24  tff(c_138, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_107])).
% 1.94/1.24  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_138])).
% 1.94/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  Inference rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Ref     : 0
% 1.94/1.24  #Sup     : 30
% 1.94/1.24  #Fact    : 0
% 1.94/1.24  #Define  : 0
% 1.94/1.24  #Split   : 0
% 1.94/1.24  #Chain   : 0
% 1.94/1.24  #Close   : 0
% 1.94/1.24  
% 1.94/1.24  Ordering : KBO
% 1.94/1.24  
% 1.94/1.24  Simplification rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Subsume      : 0
% 1.94/1.24  #Demod        : 23
% 1.94/1.24  #Tautology    : 19
% 1.94/1.24  #SimpNegUnit  : 1
% 1.94/1.24  #BackRed      : 9
% 1.94/1.24  
% 1.94/1.24  #Partial instantiations: 0
% 1.94/1.24  #Strategies tried      : 1
% 1.94/1.24  
% 1.94/1.24  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.24  Preprocessing        : 0.29
% 1.94/1.24  Parsing              : 0.15
% 1.94/1.24  CNF conversion       : 0.02
% 1.94/1.24  Main loop            : 0.13
% 1.94/1.24  Inferencing          : 0.05
% 1.94/1.24  Reduction            : 0.04
% 1.94/1.24  Demodulation         : 0.03
% 1.94/1.24  BG Simplification    : 0.01
% 1.94/1.24  Subsumption          : 0.02
% 1.94/1.24  Abstraction          : 0.01
% 1.94/1.24  MUC search           : 0.00
% 1.94/1.24  Cooper               : 0.00
% 1.94/1.24  Total                : 0.45
% 1.94/1.24  Index Insertion      : 0.00
% 1.94/1.24  Index Deletion       : 0.00
% 1.94/1.24  Index Matching       : 0.00
% 1.94/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
