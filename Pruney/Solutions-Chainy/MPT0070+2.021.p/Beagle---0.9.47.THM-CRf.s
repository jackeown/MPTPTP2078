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
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 (  96 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_173,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_831,plain,(
    ! [B_63,A_64] :
      ( r1_xboole_0(B_63,A_64)
      | k3_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_842,plain,(
    k3_xboole_0('#skF_3','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_831,c_26])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_357,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_395,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_357])).

tff(c_400,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_395])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [A_39,B_40] : k2_xboole_0(k4_xboole_0(A_39,B_40),A_39) = A_39 ),
    inference(resolution,[status(thm)],[c_16,c_185])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_237,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | ~ r1_xboole_0(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_156,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_156])).

tff(c_18,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_369,plain,(
    ! [A_46,B_47] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k2_xboole_0(k4_xboole_0(A_46,B_47),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_18])).

tff(c_2023,plain,(
    ! [A_87,B_88] : k2_xboole_0(k4_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_2,c_369])).

tff(c_2116,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2023])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2178,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_12])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_197,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_496,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k4_xboole_0(A_52,B_53),C_54) = k4_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1168,plain,(
    ! [A_72,B_73,C_74] : r1_tarski(k4_xboole_0(A_72,k2_xboole_0(B_73,C_74)),k4_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_16])).

tff(c_1365,plain,(
    ! [A_77] : r1_tarski(k4_xboole_0(A_77,'#skF_2'),k4_xboole_0(A_77,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_1168])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1412,plain,(
    ! [A_77] : k2_xboole_0(k4_xboole_0(A_77,'#skF_2'),k4_xboole_0(A_77,'#skF_1')) = k4_xboole_0(A_77,'#skF_1') ),
    inference(resolution,[status(thm)],[c_1365,c_10])).

tff(c_2204,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_1412])).

tff(c_2235,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_2204])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2453,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_24])).

tff(c_2474,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_2453])).

tff(c_2476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_2474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.56  
% 3.40/1.56  %Foreground sorts:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Background operators:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Foreground operators:
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.56  
% 3.40/1.57  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.40/1.57  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.40/1.57  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.40/1.57  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.40/1.57  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.40/1.57  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.40/1.57  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.40/1.57  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.40/1.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.40/1.57  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.40/1.57  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.40/1.57  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.40/1.57  tff(c_173, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.57  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.57  tff(c_831, plain, (![B_63, A_64]: (r1_xboole_0(B_63, A_64) | k3_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_173, c_8])).
% 3.40/1.57  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.40/1.57  tff(c_842, plain, (k3_xboole_0('#skF_3', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_831, c_26])).
% 3.40/1.57  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.57  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.57  tff(c_357, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.57  tff(c_395, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_357])).
% 3.40/1.57  tff(c_400, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_395])).
% 3.40/1.57  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.57  tff(c_185, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.57  tff(c_231, plain, (![A_39, B_40]: (k2_xboole_0(k4_xboole_0(A_39, B_40), A_39)=A_39)), inference(resolution, [status(thm)], [c_16, c_185])).
% 3.40/1.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.57  tff(c_237, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(A_39, B_40))=A_39)), inference(superposition, [status(thm), theory('equality')], [c_231, c_2])).
% 3.40/1.57  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.40/1.57  tff(c_108, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | ~r1_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.57  tff(c_111, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_108])).
% 3.40/1.57  tff(c_156, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.57  tff(c_163, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_156])).
% 3.40/1.57  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.57  tff(c_369, plain, (![A_46, B_47]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k2_xboole_0(k4_xboole_0(A_46, B_47), A_46))), inference(superposition, [status(thm), theory('equality')], [c_357, c_18])).
% 3.40/1.57  tff(c_2023, plain, (![A_87, B_88]: (k2_xboole_0(k4_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_2, c_369])).
% 3.40/1.57  tff(c_2116, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_163, c_2023])).
% 3.40/1.57  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.57  tff(c_2178, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2116, c_12])).
% 3.40/1.57  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.40/1.57  tff(c_197, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_185])).
% 3.40/1.57  tff(c_496, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k4_xboole_0(A_52, B_53), C_54)=k4_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.57  tff(c_1168, plain, (![A_72, B_73, C_74]: (r1_tarski(k4_xboole_0(A_72, k2_xboole_0(B_73, C_74)), k4_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_496, c_16])).
% 3.40/1.57  tff(c_1365, plain, (![A_77]: (r1_tarski(k4_xboole_0(A_77, '#skF_2'), k4_xboole_0(A_77, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_1168])).
% 3.40/1.57  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.57  tff(c_1412, plain, (![A_77]: (k2_xboole_0(k4_xboole_0(A_77, '#skF_2'), k4_xboole_0(A_77, '#skF_1'))=k4_xboole_0(A_77, '#skF_1'))), inference(resolution, [status(thm)], [c_1365, c_10])).
% 3.40/1.57  tff(c_2204, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2178, c_1412])).
% 3.40/1.57  tff(c_2235, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_2204])).
% 3.40/1.57  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.57  tff(c_2453, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2235, c_24])).
% 3.40/1.57  tff(c_2474, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_400, c_2453])).
% 3.40/1.57  tff(c_2476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_842, c_2474])).
% 3.40/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  Inference rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Ref     : 0
% 3.40/1.57  #Sup     : 607
% 3.40/1.57  #Fact    : 0
% 3.40/1.57  #Define  : 0
% 3.40/1.57  #Split   : 0
% 3.40/1.57  #Chain   : 0
% 3.40/1.57  #Close   : 0
% 3.40/1.57  
% 3.40/1.57  Ordering : KBO
% 3.40/1.57  
% 3.40/1.57  Simplification rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Subsume      : 1
% 3.40/1.57  #Demod        : 475
% 3.40/1.57  #Tautology    : 443
% 3.40/1.57  #SimpNegUnit  : 1
% 3.40/1.57  #BackRed      : 2
% 3.40/1.57  
% 3.40/1.57  #Partial instantiations: 0
% 3.40/1.57  #Strategies tried      : 1
% 3.40/1.57  
% 3.40/1.57  Timing (in seconds)
% 3.40/1.57  ----------------------
% 3.40/1.57  Preprocessing        : 0.26
% 3.40/1.57  Parsing              : 0.14
% 3.40/1.57  CNF conversion       : 0.02
% 3.40/1.57  Main loop            : 0.51
% 3.40/1.57  Inferencing          : 0.18
% 3.40/1.57  Reduction            : 0.21
% 3.40/1.57  Demodulation         : 0.17
% 3.40/1.57  BG Simplification    : 0.02
% 3.40/1.57  Subsumption          : 0.07
% 3.40/1.57  Abstraction          : 0.03
% 3.40/1.57  MUC search           : 0.00
% 3.40/1.57  Cooper               : 0.00
% 3.40/1.57  Total                : 0.80
% 3.40/1.57  Index Insertion      : 0.00
% 3.40/1.57  Index Deletion       : 0.00
% 3.40/1.57  Index Matching       : 0.00
% 3.40/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
