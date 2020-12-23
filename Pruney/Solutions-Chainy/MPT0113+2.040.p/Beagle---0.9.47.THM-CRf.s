%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  86 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_3124,plain,(
    ! [A_139,B_140] :
      ( r1_xboole_0(A_139,B_140)
      | k3_xboole_0(A_139,B_140) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_272,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_264,c_119])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_156,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_156])).

tff(c_1213,plain,(
    ! [A_85,B_86,C_87] : k2_xboole_0(k4_xboole_0(A_85,B_86),k3_xboole_0(A_85,C_87)) = k4_xboole_0(A_85,k4_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2667,plain,(
    ! [A_125,B_126,C_127] : k4_xboole_0(k4_xboole_0(A_125,B_126),k4_xboole_0(A_125,k4_xboole_0(B_126,C_127))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_20])).

tff(c_2819,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2667])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2920,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2819,c_22])).

tff(c_2951,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_2920])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_2951])).

tff(c_2954,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_3132,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3124,c_2954])).

tff(c_3181,plain,(
    ! [A_144,B_145] : k4_xboole_0(A_144,k4_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3214,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3181])).

tff(c_3220,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3214])).

tff(c_3647,plain,(
    ! [A_162,B_163,C_164] : k2_xboole_0(k4_xboole_0(A_162,B_163),k3_xboole_0(A_162,C_164)) = k4_xboole_0(A_162,k4_xboole_0(B_163,C_164)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3686,plain,(
    ! [A_13,C_164] : k4_xboole_0(A_13,k4_xboole_0(A_13,C_164)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_13,C_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3220,c_3647])).

tff(c_6511,plain,(
    ! [A_220,C_221] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_220,C_221)) = k3_xboole_0(A_220,C_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3686])).

tff(c_2956,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k1_xboole_0
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2964,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_2956])).

tff(c_2955,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2963,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2955,c_2956])).

tff(c_3991,plain,(
    ! [C_174] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_174)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2963,c_3647])).

tff(c_4032,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2964,c_3991])).

tff(c_6524,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_4032])).

tff(c_6592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3132,c_6524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:56:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/2.01  
% 4.74/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/2.01  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.74/2.01  
% 4.74/2.01  %Foreground sorts:
% 4.74/2.01  
% 4.74/2.01  
% 4.74/2.01  %Background operators:
% 4.74/2.01  
% 4.74/2.01  
% 4.74/2.01  %Foreground operators:
% 4.74/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.74/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.74/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.74/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.74/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.74/2.01  
% 4.74/2.02  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.74/2.02  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.74/2.02  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.74/2.02  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.74/2.02  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.74/2.02  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.74/2.02  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.74/2.02  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.74/2.02  tff(c_3124, plain, (![A_139, B_140]: (r1_xboole_0(A_139, B_140) | k3_xboole_0(A_139, B_140)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/2.02  tff(c_264, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/2.02  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.74/2.02  tff(c_119, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 4.74/2.02  tff(c_272, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_264, c_119])).
% 4.74/2.02  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.74/2.02  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.74/2.02  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.74/2.02  tff(c_156, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/2.02  tff(c_160, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_156])).
% 4.74/2.02  tff(c_1213, plain, (![A_85, B_86, C_87]: (k2_xboole_0(k4_xboole_0(A_85, B_86), k3_xboole_0(A_85, C_87))=k4_xboole_0(A_85, k4_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.74/2.02  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.74/2.02  tff(c_2667, plain, (![A_125, B_126, C_127]: (k4_xboole_0(k4_xboole_0(A_125, B_126), k4_xboole_0(A_125, k4_xboole_0(B_126, C_127)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1213, c_20])).
% 4.74/2.02  tff(c_2819, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_160, c_2667])).
% 4.74/2.02  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.74/2.02  tff(c_2920, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2819, c_22])).
% 4.74/2.02  tff(c_2951, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_2920])).
% 4.74/2.02  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_2951])).
% 4.74/2.02  tff(c_2954, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 4.74/2.02  tff(c_3132, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3124, c_2954])).
% 4.74/2.02  tff(c_3181, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k4_xboole_0(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.74/2.02  tff(c_3214, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3181])).
% 4.74/2.02  tff(c_3220, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3214])).
% 4.74/2.02  tff(c_3647, plain, (![A_162, B_163, C_164]: (k2_xboole_0(k4_xboole_0(A_162, B_163), k3_xboole_0(A_162, C_164))=k4_xboole_0(A_162, k4_xboole_0(B_163, C_164)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.74/2.02  tff(c_3686, plain, (![A_13, C_164]: (k4_xboole_0(A_13, k4_xboole_0(A_13, C_164))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_13, C_164)))), inference(superposition, [status(thm), theory('equality')], [c_3220, c_3647])).
% 4.74/2.02  tff(c_6511, plain, (![A_220, C_221]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_220, C_221))=k3_xboole_0(A_220, C_221))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3686])).
% 4.74/2.02  tff(c_2956, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k1_xboole_0 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/2.02  tff(c_2964, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_2956])).
% 4.74/2.02  tff(c_2955, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 4.74/2.02  tff(c_2963, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2955, c_2956])).
% 4.74/2.02  tff(c_3991, plain, (![C_174]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_174))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_174)))), inference(superposition, [status(thm), theory('equality')], [c_2963, c_3647])).
% 4.74/2.02  tff(c_4032, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2964, c_3991])).
% 4.74/2.02  tff(c_6524, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6511, c_4032])).
% 4.74/2.02  tff(c_6592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3132, c_6524])).
% 4.74/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/2.02  
% 4.74/2.02  Inference rules
% 4.74/2.02  ----------------------
% 4.74/2.02  #Ref     : 0
% 4.74/2.02  #Sup     : 1638
% 4.74/2.02  #Fact    : 0
% 4.74/2.02  #Define  : 0
% 4.74/2.02  #Split   : 1
% 4.74/2.02  #Chain   : 0
% 4.74/2.02  #Close   : 0
% 4.74/2.02  
% 4.74/2.02  Ordering : KBO
% 4.74/2.02  
% 4.74/2.02  Simplification rules
% 4.74/2.02  ----------------------
% 4.74/2.02  #Subsume      : 0
% 4.74/2.02  #Demod        : 1411
% 4.74/2.02  #Tautology    : 1183
% 4.74/2.02  #SimpNegUnit  : 2
% 4.74/2.02  #BackRed      : 20
% 4.74/2.02  
% 4.74/2.02  #Partial instantiations: 0
% 4.74/2.02  #Strategies tried      : 1
% 4.74/2.02  
% 4.74/2.02  Timing (in seconds)
% 4.74/2.02  ----------------------
% 4.74/2.02  Preprocessing        : 0.29
% 4.74/2.02  Parsing              : 0.17
% 4.74/2.02  CNF conversion       : 0.02
% 4.74/2.02  Main loop            : 0.88
% 4.74/2.02  Inferencing          : 0.28
% 4.74/2.02  Reduction            : 0.39
% 4.74/2.02  Demodulation         : 0.31
% 4.74/2.02  BG Simplification    : 0.03
% 4.74/2.03  Subsumption          : 0.13
% 4.74/2.03  Abstraction          : 0.04
% 4.74/2.03  MUC search           : 0.00
% 4.74/2.03  Cooper               : 0.00
% 4.74/2.03  Total                : 1.19
% 4.74/2.03  Index Insertion      : 0.00
% 4.74/2.03  Index Deletion       : 0.00
% 4.74/2.03  Index Matching       : 0.00
% 4.74/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
