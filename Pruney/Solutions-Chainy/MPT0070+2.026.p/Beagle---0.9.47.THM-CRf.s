%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:21 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :   28 (  37 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_281,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_288,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_281,c_26])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_143,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_339,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_377,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_339])).

tff(c_388,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_377])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_172,plain,(
    ! [A_34] : k4_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [A_35] : r1_tarski(k1_xboole_0,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_205,plain,(
    ! [A_35] : k4_xboole_0(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_12])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_289,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_289])).

tff(c_575,plain,(
    ! [A_56,B_57,C_58] : k4_xboole_0(k3_xboole_0(A_56,B_57),C_58) = k3_xboole_0(A_56,k4_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_618,plain,(
    ! [C_58] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_58)) = k4_xboole_0(k1_xboole_0,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_575])).

tff(c_925,plain,(
    ! [C_66] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_66)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_618])).

tff(c_1139,plain,(
    ! [B_69] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_69)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_925])).

tff(c_1259,plain,(
    ! [B_71] : k3_xboole_0('#skF_3',k3_xboole_0(B_71,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1139])).

tff(c_1295,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_1259])).

tff(c_1478,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1295,c_2])).

tff(c_1497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_1478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.42  
% 2.71/1.42  %Foreground sorts:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Background operators:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Foreground operators:
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.42  
% 2.93/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.93/1.43  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.93/1.43  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.93/1.43  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.93/1.43  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.93/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.93/1.43  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.93/1.43  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.93/1.43  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.93/1.43  tff(c_281, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.43  tff(c_288, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_281, c_26])).
% 2.93/1.43  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.43  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.43  tff(c_143, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.43  tff(c_155, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_143])).
% 2.93/1.43  tff(c_339, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.43  tff(c_377, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155, c_339])).
% 2.93/1.43  tff(c_388, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_377])).
% 2.93/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.43  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.43  tff(c_47, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.43  tff(c_50, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_47])).
% 2.93/1.43  tff(c_172, plain, (![A_34]: (k4_xboole_0(A_34, A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_143])).
% 2.93/1.43  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.43  tff(c_201, plain, (![A_35]: (r1_tarski(k1_xboole_0, A_35))), inference(superposition, [status(thm), theory('equality')], [c_172, c_16])).
% 2.93/1.43  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.43  tff(c_205, plain, (![A_35]: (k4_xboole_0(k1_xboole_0, A_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_201, c_12])).
% 2.93/1.43  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.43  tff(c_52, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.43  tff(c_55, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.93/1.43  tff(c_289, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_300, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_289])).
% 2.93/1.43  tff(c_575, plain, (![A_56, B_57, C_58]: (k4_xboole_0(k3_xboole_0(A_56, B_57), C_58)=k3_xboole_0(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.43  tff(c_618, plain, (![C_58]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_58))=k4_xboole_0(k1_xboole_0, C_58))), inference(superposition, [status(thm), theory('equality')], [c_300, c_575])).
% 2.93/1.43  tff(c_925, plain, (![C_66]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_66))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_205, c_618])).
% 2.93/1.43  tff(c_1139, plain, (![B_69]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_69))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_925])).
% 2.93/1.43  tff(c_1259, plain, (![B_71]: (k3_xboole_0('#skF_3', k3_xboole_0(B_71, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1139])).
% 2.93/1.43  tff(c_1295, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_388, c_1259])).
% 2.93/1.43  tff(c_1478, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1295, c_2])).
% 2.93/1.43  tff(c_1497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_1478])).
% 2.93/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.43  
% 2.93/1.43  Inference rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Ref     : 0
% 2.93/1.43  #Sup     : 378
% 2.93/1.43  #Fact    : 0
% 2.93/1.43  #Define  : 0
% 2.93/1.43  #Split   : 1
% 2.93/1.43  #Chain   : 0
% 2.93/1.43  #Close   : 0
% 2.93/1.43  
% 2.93/1.43  Ordering : KBO
% 2.93/1.43  
% 2.93/1.43  Simplification rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Subsume      : 2
% 2.93/1.43  #Demod        : 260
% 2.93/1.43  #Tautology    : 278
% 2.93/1.43  #SimpNegUnit  : 1
% 2.93/1.43  #BackRed      : 2
% 2.93/1.43  
% 2.93/1.43  #Partial instantiations: 0
% 2.93/1.43  #Strategies tried      : 1
% 2.93/1.43  
% 2.93/1.43  Timing (in seconds)
% 2.93/1.43  ----------------------
% 2.93/1.44  Preprocessing        : 0.28
% 2.93/1.44  Parsing              : 0.15
% 2.93/1.44  CNF conversion       : 0.02
% 2.93/1.44  Main loop            : 0.40
% 2.93/1.44  Inferencing          : 0.14
% 2.93/1.44  Reduction            : 0.16
% 2.93/1.44  Demodulation         : 0.12
% 2.93/1.44  BG Simplification    : 0.02
% 2.93/1.44  Subsumption          : 0.06
% 2.93/1.44  Abstraction          : 0.02
% 2.93/1.44  MUC search           : 0.00
% 2.93/1.44  Cooper               : 0.00
% 2.93/1.44  Total                : 0.70
% 2.93/1.44  Index Insertion      : 0.00
% 2.93/1.44  Index Deletion       : 0.00
% 2.93/1.44  Index Matching       : 0.00
% 2.93/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
