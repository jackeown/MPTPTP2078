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
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  71 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_122,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_130,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_88,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_197,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_51,B_52)),k3_xboole_0(k1_relat_1(A_51),k1_relat_1(B_52)))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_206,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_197])).

tff(c_212,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_206])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_14])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_222,plain,(
    k1_relat_1(k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_20])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_349,plain,(
    ! [A_56,B_57] :
      ( k1_relat_1(k3_xboole_0(A_56,B_57)) != k1_xboole_0
      | k3_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_358,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_349])).

tff(c_371,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_358])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:07:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.43  
% 2.23/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.43  
% 2.23/1.43  %Foreground sorts:
% 2.23/1.43  
% 2.23/1.43  
% 2.23/1.43  %Background operators:
% 2.23/1.43  
% 2.23/1.43  
% 2.23/1.43  %Foreground operators:
% 2.23/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.43  
% 2.23/1.44  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.44  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.23/1.44  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.23/1.44  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.23/1.44  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.23/1.44  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.23/1.44  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.23/1.44  tff(c_122, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.44  tff(c_30, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.44  tff(c_130, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_30])).
% 2.23/1.44  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.44  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.44  tff(c_32, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.44  tff(c_88, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.44  tff(c_92, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_88])).
% 2.23/1.44  tff(c_197, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(k3_xboole_0(A_51, B_52)), k3_xboole_0(k1_relat_1(A_51), k1_relat_1(B_52))) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.44  tff(c_206, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_197])).
% 2.23/1.44  tff(c_212, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_206])).
% 2.23/1.44  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.44  tff(c_218, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_212, c_14])).
% 2.23/1.44  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.44  tff(c_222, plain, (k1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_218, c_20])).
% 2.23/1.44  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.44  tff(c_69, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.44  tff(c_349, plain, (![A_56, B_57]: (k1_relat_1(k3_xboole_0(A_56, B_57))!=k1_xboole_0 | k3_xboole_0(A_56, B_57)=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_22, c_69])).
% 2.23/1.44  tff(c_358, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_222, c_349])).
% 2.23/1.44  tff(c_371, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_358])).
% 2.23/1.44  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_371])).
% 2.23/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.44  
% 2.23/1.44  Inference rules
% 2.23/1.44  ----------------------
% 2.23/1.44  #Ref     : 0
% 2.23/1.44  #Sup     : 82
% 2.23/1.44  #Fact    : 0
% 2.23/1.44  #Define  : 0
% 2.23/1.44  #Split   : 5
% 2.23/1.44  #Chain   : 0
% 2.23/1.44  #Close   : 0
% 2.23/1.44  
% 2.23/1.44  Ordering : KBO
% 2.23/1.44  
% 2.23/1.44  Simplification rules
% 2.23/1.44  ----------------------
% 2.23/1.44  #Subsume      : 2
% 2.23/1.44  #Demod        : 37
% 2.23/1.44  #Tautology    : 43
% 2.23/1.44  #SimpNegUnit  : 4
% 2.23/1.44  #BackRed      : 6
% 2.23/1.44  
% 2.23/1.44  #Partial instantiations: 0
% 2.23/1.44  #Strategies tried      : 1
% 2.23/1.44  
% 2.23/1.44  Timing (in seconds)
% 2.23/1.44  ----------------------
% 2.23/1.45  Preprocessing        : 0.31
% 2.23/1.45  Parsing              : 0.18
% 2.23/1.45  CNF conversion       : 0.02
% 2.23/1.45  Main loop            : 0.25
% 2.23/1.45  Inferencing          : 0.09
% 2.23/1.45  Reduction            : 0.07
% 2.23/1.45  Demodulation         : 0.05
% 2.23/1.45  BG Simplification    : 0.01
% 2.23/1.45  Subsumption          : 0.04
% 2.23/1.45  Abstraction          : 0.01
% 2.23/1.45  MUC search           : 0.00
% 2.23/1.45  Cooper               : 0.00
% 2.23/1.45  Total                : 0.59
% 2.23/1.45  Index Insertion      : 0.00
% 2.23/1.45  Index Deletion       : 0.00
% 2.23/1.45  Index Matching       : 0.00
% 2.23/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
