%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 182 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :   58 ( 190 expanded)
%              Number of equality atoms :   51 ( 173 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_28,k1_xboole_0)) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_102])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_29] : k2_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_126,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_114,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_102])).

tff(c_230,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_114])).

tff(c_443,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_929,plain,(
    ! [C_52] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_52)) = k4_xboole_0('#skF_3',C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_443])).

tff(c_2081,plain,(
    ! [A_74] : k4_xboole_0('#skF_3',k2_xboole_0(A_74,'#skF_2')) = k4_xboole_0('#skF_3',A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_929])).

tff(c_26,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,(
    ! [B_7] : k4_xboole_0(B_7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_200,plain,(
    ! [B_32] : k4_xboole_0(B_32,k1_xboole_0) = B_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_146])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    ! [B_32] : k4_xboole_0(B_32,B_32) = k3_xboole_0(B_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_16])).

tff(c_217,plain,(
    ! [B_32] : k4_xboole_0(B_32,B_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_206])).

tff(c_487,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_443])).

tff(c_850,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k2_xboole_0(B_51,A_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_487])).

tff(c_1031,plain,(
    ! [B_54,A_55] : k4_xboole_0(B_54,k2_xboole_0(B_54,A_55)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_850])).

tff(c_1094,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1031])).

tff(c_2093,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2081,c_1094])).

tff(c_2189,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_10])).

tff(c_2197,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2189])).

tff(c_909,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_850])).

tff(c_172,plain,(
    ! [B_7] : k4_xboole_0(B_7,k1_xboole_0) = B_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_146])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_291,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_309,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_291])).

tff(c_320,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_309])).

tff(c_543,plain,(
    ! [C_41] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_41)) = k4_xboole_0('#skF_1',C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_443])).

tff(c_3948,plain,(
    ! [B_98] : k4_xboole_0('#skF_1',k2_xboole_0(B_98,'#skF_2')) = k4_xboole_0('#skF_1',B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_543])).

tff(c_4024,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3948])).

tff(c_4045,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_4024])).

tff(c_4073,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4045,c_10])).

tff(c_4083,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2197,c_152,c_2,c_4073])).

tff(c_4085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_4083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.74  
% 4.15/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.75  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.15/1.75  
% 4.15/1.75  %Foreground sorts:
% 4.15/1.75  
% 4.15/1.75  
% 4.15/1.75  %Background operators:
% 4.15/1.75  
% 4.15/1.75  
% 4.15/1.75  %Foreground operators:
% 4.15/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.15/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.15/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.15/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.15/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.15/1.75  
% 4.22/1.77  tff(f_52, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 4.22/1.77  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.22/1.77  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.22/1.77  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.22/1.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.22/1.77  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.22/1.77  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.22/1.77  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.22/1.77  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.22/1.77  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.22/1.77  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.22/1.77  tff(c_102, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.22/1.77  tff(c_120, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_28, k1_xboole_0))=A_28)), inference(superposition, [status(thm), theory('equality')], [c_8, c_102])).
% 4.22/1.77  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.22/1.77  tff(c_136, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 4.22/1.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.77  tff(c_152, plain, (![A_29]: (k2_xboole_0(A_29, k1_xboole_0)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 4.22/1.77  tff(c_126, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, A_28)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 4.22/1.77  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.22/1.77  tff(c_71, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.77  tff(c_78, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_71])).
% 4.22/1.77  tff(c_114, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_78, c_102])).
% 4.22/1.77  tff(c_230, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_126, c_114])).
% 4.22/1.77  tff(c_443, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.22/1.77  tff(c_929, plain, (![C_52]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_52))=k4_xboole_0('#skF_3', C_52))), inference(superposition, [status(thm), theory('equality')], [c_230, c_443])).
% 4.22/1.77  tff(c_2081, plain, (![A_74]: (k4_xboole_0('#skF_3', k2_xboole_0(A_74, '#skF_2'))=k4_xboole_0('#skF_3', A_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_929])).
% 4.22/1.77  tff(c_26, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.22/1.77  tff(c_146, plain, (![B_7]: (k4_xboole_0(B_7, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 4.22/1.77  tff(c_200, plain, (![B_32]: (k4_xboole_0(B_32, k1_xboole_0)=B_32)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_146])).
% 4.22/1.77  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.22/1.77  tff(c_206, plain, (![B_32]: (k4_xboole_0(B_32, B_32)=k3_xboole_0(B_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_16])).
% 4.22/1.77  tff(c_217, plain, (![B_32]: (k4_xboole_0(B_32, B_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_206])).
% 4.22/1.77  tff(c_487, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_443])).
% 4.22/1.77  tff(c_850, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k2_xboole_0(B_51, A_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_487])).
% 4.22/1.77  tff(c_1031, plain, (![B_54, A_55]: (k4_xboole_0(B_54, k2_xboole_0(B_54, A_55))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_850])).
% 4.22/1.77  tff(c_1094, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_1031])).
% 4.22/1.77  tff(c_2093, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2081, c_1094])).
% 4.22/1.77  tff(c_2189, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2093, c_10])).
% 4.22/1.77  tff(c_2197, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2189])).
% 4.22/1.77  tff(c_909, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_850])).
% 4.22/1.77  tff(c_172, plain, (![B_7]: (k4_xboole_0(B_7, k1_xboole_0)=B_7)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_146])).
% 4.22/1.77  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.22/1.77  tff(c_79, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_71])).
% 4.22/1.77  tff(c_291, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.77  tff(c_309, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_291])).
% 4.22/1.77  tff(c_320, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_309])).
% 4.22/1.77  tff(c_543, plain, (![C_41]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_41))=k4_xboole_0('#skF_1', C_41))), inference(superposition, [status(thm), theory('equality')], [c_320, c_443])).
% 4.22/1.77  tff(c_3948, plain, (![B_98]: (k4_xboole_0('#skF_1', k2_xboole_0(B_98, '#skF_2'))=k4_xboole_0('#skF_1', B_98))), inference(superposition, [status(thm), theory('equality')], [c_2, c_543])).
% 4.22/1.77  tff(c_4024, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_3948])).
% 4.22/1.77  tff(c_4045, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_909, c_4024])).
% 4.22/1.77  tff(c_4073, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4045, c_10])).
% 4.22/1.77  tff(c_4083, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2197, c_152, c_2, c_4073])).
% 4.22/1.77  tff(c_4085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_4083])).
% 4.22/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.77  
% 4.22/1.77  Inference rules
% 4.22/1.77  ----------------------
% 4.22/1.77  #Ref     : 0
% 4.22/1.77  #Sup     : 995
% 4.22/1.77  #Fact    : 0
% 4.22/1.77  #Define  : 0
% 4.22/1.77  #Split   : 0
% 4.22/1.77  #Chain   : 0
% 4.22/1.77  #Close   : 0
% 4.22/1.77  
% 4.22/1.77  Ordering : KBO
% 4.22/1.77  
% 4.22/1.77  Simplification rules
% 4.22/1.77  ----------------------
% 4.22/1.77  #Subsume      : 0
% 4.22/1.77  #Demod        : 946
% 4.22/1.77  #Tautology    : 771
% 4.22/1.77  #SimpNegUnit  : 1
% 4.22/1.77  #BackRed      : 2
% 4.22/1.77  
% 4.22/1.77  #Partial instantiations: 0
% 4.22/1.77  #Strategies tried      : 1
% 4.22/1.77  
% 4.22/1.77  Timing (in seconds)
% 4.22/1.77  ----------------------
% 4.22/1.78  Preprocessing        : 0.27
% 4.22/1.78  Parsing              : 0.15
% 4.22/1.78  CNF conversion       : 0.02
% 4.22/1.78  Main loop            : 0.71
% 4.22/1.78  Inferencing          : 0.22
% 4.22/1.78  Reduction            : 0.34
% 4.22/1.78  Demodulation         : 0.29
% 4.22/1.78  BG Simplification    : 0.02
% 4.22/1.78  Subsumption          : 0.09
% 4.22/1.78  Abstraction          : 0.03
% 4.22/1.78  MUC search           : 0.00
% 4.22/1.78  Cooper               : 0.00
% 4.22/1.78  Total                : 1.03
% 4.22/1.78  Index Insertion      : 0.00
% 4.22/1.78  Index Deletion       : 0.00
% 4.22/1.78  Index Matching       : 0.00
% 4.22/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
