%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k3_xboole_0(k1_relat_1(B_4),A_3) = k1_relat_1(k7_relat_1(B_4,A_3))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = k7_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_41,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_53,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  %$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.63/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.17  
% 1.63/1.18  tff(f_42, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_1)).
% 1.63/1.18  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.63/1.18  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.63/1.18  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.18  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(k1_relat_1(B_4), A_3)=k1_relat_1(k7_relat_1(B_4, A_3)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.18  tff(c_6, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=k7_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.18  tff(c_8, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.18  tff(c_39, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_8])).
% 1.63/1.18  tff(c_41, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_39])).
% 1.63/1.18  tff(c_53, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 1.63/1.18  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 1.63/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.18  
% 1.63/1.18  Inference rules
% 1.63/1.18  ----------------------
% 1.63/1.18  #Ref     : 0
% 1.63/1.18  #Sup     : 10
% 1.63/1.18  #Fact    : 0
% 1.63/1.18  #Define  : 0
% 1.63/1.18  #Split   : 0
% 1.63/1.18  #Chain   : 0
% 1.63/1.18  #Close   : 0
% 1.63/1.18  
% 1.63/1.18  Ordering : KBO
% 1.63/1.18  
% 1.63/1.18  Simplification rules
% 1.63/1.18  ----------------------
% 1.63/1.18  #Subsume      : 0
% 1.63/1.18  #Demod        : 2
% 1.63/1.18  #Tautology    : 6
% 1.63/1.18  #SimpNegUnit  : 0
% 1.63/1.18  #BackRed      : 0
% 1.63/1.18  
% 1.63/1.18  #Partial instantiations: 0
% 1.63/1.18  #Strategies tried      : 1
% 1.63/1.18  
% 1.63/1.18  Timing (in seconds)
% 1.63/1.18  ----------------------
% 1.63/1.18  Preprocessing        : 0.29
% 1.63/1.18  Parsing              : 0.15
% 1.63/1.18  CNF conversion       : 0.02
% 1.63/1.18  Main loop            : 0.07
% 1.63/1.18  Inferencing          : 0.04
% 1.63/1.18  Reduction            : 0.02
% 1.63/1.18  Demodulation         : 0.02
% 1.63/1.18  BG Simplification    : 0.01
% 1.63/1.18  Subsumption          : 0.01
% 1.63/1.18  Abstraction          : 0.01
% 1.63/1.18  MUC search           : 0.00
% 1.63/1.18  Cooper               : 0.00
% 1.63/1.18  Total                : 0.39
% 1.63/1.18  Index Insertion      : 0.00
% 1.78/1.18  Index Deletion       : 0.00
% 1.78/1.18  Index Matching       : 0.00
% 1.78/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
