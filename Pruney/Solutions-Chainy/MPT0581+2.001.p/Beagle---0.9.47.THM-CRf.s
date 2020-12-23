%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  46 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C,D] :
                ( ( k7_relat_1(A,C) = k7_relat_1(B,C)
                  & k7_relat_1(A,D) = k7_relat_1(B,D) )
               => k7_relat_1(A,k2_xboole_0(C,D)) = k7_relat_1(B,k2_xboole_0(C,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).

tff(c_4,plain,(
    k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,(
    ! [C_11,A_12,B_13] :
      ( k2_xboole_0(k7_relat_1(C_11,A_12),k7_relat_1(C_11,B_13)) = k7_relat_1(C_11,k2_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_12] :
      ( k2_xboole_0(k7_relat_1('#skF_2',A_12),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0(A_12,'#skF_4'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21])).

tff(c_65,plain,(
    ! [A_15] : k2_xboole_0(k7_relat_1('#skF_2',A_15),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0(A_15,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_74,plain,(
    k2_xboole_0(k7_relat_1('#skF_1','#skF_3'),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( k2_xboole_0(k7_relat_1(C_3,A_1),k7_relat_1(C_3,B_2)) = k7_relat_1(C_3,k2_xboole_0(A_1,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,
    ( k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_163,plain,(
    k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_156])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.36  
% 2.00/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.36  %$ v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.36  
% 2.00/1.36  %Foreground sorts:
% 2.00/1.36  
% 2.00/1.36  
% 2.00/1.36  %Background operators:
% 2.00/1.36  
% 2.00/1.36  
% 2.00/1.36  %Foreground operators:
% 2.00/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.36  
% 2.10/1.37  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C, D]: (((k7_relat_1(A, C) = k7_relat_1(B, C)) & (k7_relat_1(A, D) = k7_relat_1(B, D))) => (k7_relat_1(A, k2_xboole_0(C, D)) = k7_relat_1(B, k2_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_relat_1)).
% 2.10/1.37  tff(f_29, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_relat_1)).
% 2.10/1.37  tff(c_4, plain, (k7_relat_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.37  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.37  tff(c_8, plain, (k7_relat_1('#skF_2', '#skF_3')=k7_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.37  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.37  tff(c_6, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.37  tff(c_21, plain, (![C_11, A_12, B_13]: (k2_xboole_0(k7_relat_1(C_11, A_12), k7_relat_1(C_11, B_13))=k7_relat_1(C_11, k2_xboole_0(A_12, B_13)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.37  tff(c_39, plain, (![A_12]: (k2_xboole_0(k7_relat_1('#skF_2', A_12), k7_relat_1('#skF_1', '#skF_4'))=k7_relat_1('#skF_2', k2_xboole_0(A_12, '#skF_4')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21])).
% 2.10/1.37  tff(c_65, plain, (![A_15]: (k2_xboole_0(k7_relat_1('#skF_2', A_15), k7_relat_1('#skF_1', '#skF_4'))=k7_relat_1('#skF_2', k2_xboole_0(A_15, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_39])).
% 2.10/1.37  tff(c_74, plain, (k2_xboole_0(k7_relat_1('#skF_1', '#skF_3'), k7_relat_1('#skF_1', '#skF_4'))=k7_relat_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 2.10/1.37  tff(c_2, plain, (![C_3, A_1, B_2]: (k2_xboole_0(k7_relat_1(C_3, A_1), k7_relat_1(C_3, B_2))=k7_relat_1(C_3, k2_xboole_0(A_1, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.37  tff(c_156, plain, (k7_relat_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 2.10/1.37  tff(c_163, plain, (k7_relat_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_156])).
% 2.10/1.37  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_163])).
% 2.10/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.37  
% 2.10/1.37  Inference rules
% 2.10/1.37  ----------------------
% 2.10/1.37  #Ref     : 0
% 2.10/1.37  #Sup     : 42
% 2.10/1.37  #Fact    : 0
% 2.10/1.37  #Define  : 0
% 2.10/1.37  #Split   : 0
% 2.10/1.37  #Chain   : 0
% 2.10/1.37  #Close   : 0
% 2.10/1.37  
% 2.10/1.37  Ordering : KBO
% 2.10/1.37  
% 2.10/1.37  Simplification rules
% 2.10/1.37  ----------------------
% 2.10/1.37  #Subsume      : 0
% 2.10/1.37  #Demod        : 12
% 2.10/1.37  #Tautology    : 20
% 2.10/1.37  #SimpNegUnit  : 1
% 2.10/1.37  #BackRed      : 1
% 2.10/1.37  
% 2.10/1.37  #Partial instantiations: 0
% 2.10/1.37  #Strategies tried      : 1
% 2.10/1.37  
% 2.10/1.37  Timing (in seconds)
% 2.10/1.37  ----------------------
% 2.10/1.38  Preprocessing        : 0.31
% 2.10/1.38  Parsing              : 0.17
% 2.10/1.38  CNF conversion       : 0.02
% 2.10/1.38  Main loop            : 0.18
% 2.10/1.38  Inferencing          : 0.07
% 2.10/1.38  Reduction            : 0.07
% 2.10/1.38  Demodulation         : 0.05
% 2.10/1.38  BG Simplification    : 0.01
% 2.10/1.38  Subsumption          : 0.03
% 2.10/1.38  Abstraction          : 0.01
% 2.10/1.38  MUC search           : 0.00
% 2.10/1.38  Cooper               : 0.00
% 2.10/1.38  Total                : 0.52
% 2.10/1.38  Index Insertion      : 0.00
% 2.10/1.38  Index Deletion       : 0.00
% 2.10/1.38  Index Matching       : 0.00
% 2.10/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
