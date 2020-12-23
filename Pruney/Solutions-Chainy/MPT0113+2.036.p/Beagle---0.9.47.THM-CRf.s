%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  83 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_1033,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(A_78,B_79)
      | k3_xboole_0(A_78,B_79) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_244,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_232,c_45])).

tff(c_24,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_126,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k4_xboole_0(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_496,plain,(
    ! [A_54,B_55,C_56] : k3_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k3_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_762,plain,(
    ! [C_65] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_65)) = k3_xboole_0('#skF_1',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_496])).

tff(c_781,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_762])).

tff(c_806,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_781])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_872,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_12])).

tff(c_875,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_872])).

tff(c_877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_875])).

tff(c_878,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1041,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1033,c_878])).

tff(c_18,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_984,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_988,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_984])).

tff(c_927,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_938,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_927])).

tff(c_1279,plain,(
    ! [A_93,B_94,C_95] : k3_xboole_0(k3_xboole_0(A_93,B_94),C_95) = k3_xboole_0(A_93,k3_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1478,plain,(
    ! [C_100] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_100)) = k3_xboole_0('#skF_1',C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_1279])).

tff(c_1502,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1478])).

tff(c_1521,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1502])).

tff(c_1523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_1521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.51  
% 2.90/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.51  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.51  
% 2.90/1.51  %Foreground sorts:
% 2.90/1.51  
% 2.90/1.51  
% 2.90/1.51  %Background operators:
% 2.90/1.51  
% 2.90/1.51  
% 2.90/1.51  %Foreground operators:
% 2.90/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.51  
% 2.90/1.52  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.90/1.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.90/1.52  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.90/1.52  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.90/1.52  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.90/1.52  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.90/1.52  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.90/1.52  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.90/1.52  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.90/1.52  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.90/1.52  tff(c_1033, plain, (![A_78, B_79]: (r1_xboole_0(A_78, B_79) | k3_xboole_0(A_78, B_79)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.52  tff(c_232, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.52  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.52  tff(c_45, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.90/1.52  tff(c_244, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_232, c_45])).
% 2.90/1.52  tff(c_24, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.52  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.52  tff(c_126, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.52  tff(c_133, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.90/1.52  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.52  tff(c_134, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k4_xboole_0(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_126])).
% 2.90/1.52  tff(c_496, plain, (![A_54, B_55, C_56]: (k3_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k3_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.52  tff(c_762, plain, (![C_65]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_65))=k3_xboole_0('#skF_1', C_65))), inference(superposition, [status(thm), theory('equality')], [c_133, c_496])).
% 2.90/1.52  tff(c_781, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_134, c_762])).
% 2.90/1.52  tff(c_806, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_781])).
% 2.90/1.52  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.52  tff(c_872, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_806, c_12])).
% 2.90/1.52  tff(c_875, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_872])).
% 2.90/1.52  tff(c_877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_875])).
% 2.90/1.52  tff(c_878, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.90/1.52  tff(c_1041, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1033, c_878])).
% 2.90/1.52  tff(c_18, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.90/1.52  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.52  tff(c_984, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.52  tff(c_988, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_984])).
% 2.90/1.52  tff(c_927, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.52  tff(c_938, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_927])).
% 2.90/1.52  tff(c_1279, plain, (![A_93, B_94, C_95]: (k3_xboole_0(k3_xboole_0(A_93, B_94), C_95)=k3_xboole_0(A_93, k3_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.52  tff(c_1478, plain, (![C_100]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_100))=k3_xboole_0('#skF_1', C_100))), inference(superposition, [status(thm), theory('equality')], [c_938, c_1279])).
% 2.90/1.52  tff(c_1502, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_988, c_1478])).
% 2.90/1.52  tff(c_1521, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1502])).
% 2.90/1.52  tff(c_1523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1041, c_1521])).
% 2.90/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.52  
% 2.90/1.52  Inference rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Ref     : 0
% 2.90/1.52  #Sup     : 377
% 2.90/1.52  #Fact    : 0
% 2.90/1.52  #Define  : 0
% 2.90/1.52  #Split   : 1
% 2.90/1.52  #Chain   : 0
% 2.90/1.52  #Close   : 0
% 2.90/1.52  
% 2.90/1.52  Ordering : KBO
% 2.90/1.52  
% 2.90/1.52  Simplification rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Subsume      : 0
% 2.90/1.52  #Demod        : 224
% 2.90/1.52  #Tautology    : 277
% 2.90/1.52  #SimpNegUnit  : 2
% 2.90/1.52  #BackRed      : 0
% 2.90/1.52  
% 2.90/1.52  #Partial instantiations: 0
% 2.90/1.52  #Strategies tried      : 1
% 2.90/1.52  
% 2.90/1.52  Timing (in seconds)
% 2.90/1.52  ----------------------
% 2.90/1.52  Preprocessing        : 0.28
% 2.90/1.52  Parsing              : 0.16
% 2.90/1.52  CNF conversion       : 0.02
% 2.90/1.52  Main loop            : 0.42
% 2.90/1.52  Inferencing          : 0.16
% 2.90/1.52  Reduction            : 0.16
% 2.90/1.52  Demodulation         : 0.12
% 2.90/1.52  BG Simplification    : 0.02
% 2.90/1.52  Subsumption          : 0.05
% 2.90/1.52  Abstraction          : 0.02
% 2.90/1.52  MUC search           : 0.00
% 2.90/1.53  Cooper               : 0.00
% 2.90/1.53  Total                : 0.72
% 2.90/1.53  Index Insertion      : 0.00
% 2.90/1.53  Index Deletion       : 0.00
% 2.90/1.53  Index Matching       : 0.00
% 2.90/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
