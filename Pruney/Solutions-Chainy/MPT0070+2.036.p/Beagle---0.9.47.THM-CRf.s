%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:22 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 (  94 expanded)
%              Number of equality atoms :   36 (  57 expanded)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_279,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_287,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_279,c_24])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_45])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_288,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_314,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_288])).

tff(c_325,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_314])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_343,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_387,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_343])).

tff(c_463,plain,(
    ! [A_49] : k3_xboole_0(A_49,A_49) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_387])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k4_xboole_0(A_15,B_16),k3_xboole_0(A_15,C_17)) = k4_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_469,plain,(
    ! [A_49,B_16] : k4_xboole_0(A_49,k4_xboole_0(B_16,A_49)) = k2_xboole_0(k4_xboole_0(A_49,B_16),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_22])).

tff(c_761,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(B_60,A_59)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_469])).

tff(c_815,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_761])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_390,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_343])).

tff(c_403,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_390])).

tff(c_413,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,C_48)) = k4_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_422,plain,(
    ! [B_47] : k4_xboole_0('#skF_1',k4_xboole_0(B_47,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_47),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_413])).

tff(c_455,plain,(
    ! [B_47] : k4_xboole_0('#skF_1',k4_xboole_0(B_47,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_422])).

tff(c_909,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_455])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_948,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_20])).

tff(c_960,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_948])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.39  
% 2.70/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.70/1.40  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.70/1.40  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.70/1.40  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.70/1.40  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.40  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.70/1.40  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.70/1.40  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.70/1.40  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.70/1.40  tff(c_279, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.40  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.40  tff(c_287, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_279, c_24])).
% 2.70/1.40  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.40  tff(c_45, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.40  tff(c_48, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_45])).
% 2.70/1.40  tff(c_59, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.40  tff(c_69, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_59])).
% 2.70/1.40  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.40  tff(c_50, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.40  tff(c_54, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_50])).
% 2.70/1.40  tff(c_288, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.40  tff(c_314, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54, c_288])).
% 2.70/1.40  tff(c_325, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_314])).
% 2.70/1.40  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.40  tff(c_117, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.40  tff(c_132, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_14, c_117])).
% 2.70/1.40  tff(c_343, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.70/1.40  tff(c_387, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_69, c_343])).
% 2.70/1.40  tff(c_463, plain, (![A_49]: (k3_xboole_0(A_49, A_49)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_387])).
% 2.70/1.40  tff(c_22, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k4_xboole_0(A_15, B_16), k3_xboole_0(A_15, C_17))=k4_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.40  tff(c_469, plain, (![A_49, B_16]: (k4_xboole_0(A_49, k4_xboole_0(B_16, A_49))=k2_xboole_0(k4_xboole_0(A_49, B_16), A_49))), inference(superposition, [status(thm), theory('equality')], [c_463, c_22])).
% 2.70/1.40  tff(c_761, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(B_60, A_59))=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_469])).
% 2.70/1.40  tff(c_815, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_325, c_761])).
% 2.70/1.40  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.40  tff(c_71, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.70/1.40  tff(c_390, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_343])).
% 2.70/1.40  tff(c_403, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_390])).
% 2.70/1.40  tff(c_413, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, C_48))=k4_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.40  tff(c_422, plain, (![B_47]: (k4_xboole_0('#skF_1', k4_xboole_0(B_47, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_47), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_413])).
% 2.70/1.40  tff(c_455, plain, (![B_47]: (k4_xboole_0('#skF_1', k4_xboole_0(B_47, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_422])).
% 2.70/1.40  tff(c_909, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_815, c_455])).
% 2.70/1.40  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.70/1.40  tff(c_948, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_909, c_20])).
% 2.70/1.40  tff(c_960, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_948])).
% 2.70/1.40  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_960])).
% 2.70/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  Inference rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Ref     : 0
% 2.70/1.40  #Sup     : 239
% 2.70/1.40  #Fact    : 0
% 2.70/1.40  #Define  : 0
% 2.70/1.40  #Split   : 0
% 2.70/1.40  #Chain   : 0
% 2.70/1.40  #Close   : 0
% 2.70/1.40  
% 2.70/1.40  Ordering : KBO
% 2.70/1.40  
% 2.70/1.40  Simplification rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Subsume      : 0
% 2.70/1.40  #Demod        : 138
% 2.70/1.40  #Tautology    : 164
% 2.70/1.40  #SimpNegUnit  : 1
% 2.70/1.40  #BackRed      : 0
% 2.70/1.40  
% 2.70/1.40  #Partial instantiations: 0
% 2.70/1.40  #Strategies tried      : 1
% 2.70/1.40  
% 2.70/1.40  Timing (in seconds)
% 2.70/1.40  ----------------------
% 2.70/1.40  Preprocessing        : 0.28
% 2.70/1.40  Parsing              : 0.16
% 2.70/1.40  CNF conversion       : 0.02
% 2.70/1.40  Main loop            : 0.32
% 2.70/1.40  Inferencing          : 0.13
% 2.70/1.40  Reduction            : 0.11
% 2.70/1.40  Demodulation         : 0.08
% 2.70/1.40  BG Simplification    : 0.02
% 2.70/1.40  Subsumption          : 0.05
% 2.70/1.40  Abstraction          : 0.02
% 2.70/1.40  MUC search           : 0.00
% 2.70/1.40  Cooper               : 0.00
% 2.70/1.40  Total                : 0.63
% 2.70/1.40  Index Insertion      : 0.00
% 2.70/1.40  Index Deletion       : 0.00
% 2.70/1.40  Index Matching       : 0.00
% 2.70/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
