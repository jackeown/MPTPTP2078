%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  68 expanded)
%              Number of equality atoms :   34 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_514,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_xboole_0(A_52,B_53),k4_xboole_0(A_52,B_53)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_541,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_54,k1_xboole_0)) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_514])).

tff(c_63,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_79,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_51])).

tff(c_590,plain,(
    ! [A_57] : k4_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_79])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_599,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k3_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_20])).

tff(c_605,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_599])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k4_xboole_0(A_20,B_21),k3_xboole_0(A_20,C_22)) = k4_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_272,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_276,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_272])).

tff(c_718,plain,(
    ! [A_61,B_62,C_63] : k2_xboole_0(k4_xboole_0(A_61,B_62),k3_xboole_0(A_61,C_63)) = k4_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_759,plain,(
    ! [B_62] : k4_xboole_0('#skF_1',k4_xboole_0(B_62,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_62),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_718])).

tff(c_981,plain,(
    ! [B_68] : k4_xboole_0('#skF_1',k4_xboole_0(B_68,'#skF_2')) = k4_xboole_0('#skF_1',B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_759])).

tff(c_532,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_514])).

tff(c_987,plain,(
    ! [B_68] : k2_xboole_0(k3_xboole_0(k4_xboole_0(B_68,'#skF_2'),'#skF_1'),k4_xboole_0('#skF_1',B_68)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_532])).

tff(c_1029,plain,(
    ! [B_69] : k4_xboole_0('#skF_1',k3_xboole_0(B_69,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_2,c_4,c_987])).

tff(c_1047,plain,(
    ! [B_69] : k3_xboole_0('#skF_1',k3_xboole_0(B_69,'#skF_2')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_20])).

tff(c_1076,plain,(
    ! [B_69] : k3_xboole_0('#skF_1',k3_xboole_0(B_69,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_1047])).

tff(c_365,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(A_44,B_45)
      | k3_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_29,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_373,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_365,c_29])).

tff(c_1247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.40  
% 2.83/1.41  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.83/1.41  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.83/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.83/1.41  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.83/1.41  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.83/1.41  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.83/1.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.83/1.41  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.83/1.41  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.83/1.41  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.41  tff(c_514, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, B_53), k4_xboole_0(A_52, B_53))=A_52)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.41  tff(c_541, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_54, k1_xboole_0))=A_54)), inference(superposition, [status(thm), theory('equality')], [c_16, c_514])).
% 2.83/1.41  tff(c_63, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.41  tff(c_42, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k3_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.41  tff(c_51, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_16, c_42])).
% 2.83/1.41  tff(c_79, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_63, c_51])).
% 2.83/1.41  tff(c_590, plain, (![A_57]: (k4_xboole_0(A_57, k1_xboole_0)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_541, c_79])).
% 2.83/1.41  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.41  tff(c_599, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k3_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_590, c_20])).
% 2.83/1.41  tff(c_605, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_599])).
% 2.83/1.41  tff(c_24, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k4_xboole_0(A_20, B_21), k3_xboole_0(A_20, C_22))=k4_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.41  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.41  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.41  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.41  tff(c_272, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.41  tff(c_276, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_272])).
% 2.83/1.41  tff(c_718, plain, (![A_61, B_62, C_63]: (k2_xboole_0(k4_xboole_0(A_61, B_62), k3_xboole_0(A_61, C_63))=k4_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.41  tff(c_759, plain, (![B_62]: (k4_xboole_0('#skF_1', k4_xboole_0(B_62, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_62), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_276, c_718])).
% 2.83/1.41  tff(c_981, plain, (![B_68]: (k4_xboole_0('#skF_1', k4_xboole_0(B_68, '#skF_2'))=k4_xboole_0('#skF_1', B_68))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_759])).
% 2.83/1.41  tff(c_532, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_514])).
% 2.83/1.41  tff(c_987, plain, (![B_68]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(B_68, '#skF_2'), '#skF_1'), k4_xboole_0('#skF_1', B_68))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_981, c_532])).
% 2.83/1.41  tff(c_1029, plain, (![B_69]: (k4_xboole_0('#skF_1', k3_xboole_0(B_69, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_2, c_4, c_987])).
% 2.83/1.41  tff(c_1047, plain, (![B_69]: (k3_xboole_0('#skF_1', k3_xboole_0(B_69, '#skF_2'))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_20])).
% 2.83/1.41  tff(c_1076, plain, (![B_69]: (k3_xboole_0('#skF_1', k3_xboole_0(B_69, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_605, c_1047])).
% 2.83/1.41  tff(c_365, plain, (![A_44, B_45]: (r1_xboole_0(A_44, B_45) | k3_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.41  tff(c_28, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.41  tff(c_29, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 2.83/1.41  tff(c_373, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_365, c_29])).
% 2.83/1.41  tff(c_1247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1076, c_373])).
% 2.83/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  Inference rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Ref     : 0
% 2.83/1.41  #Sup     : 297
% 2.83/1.41  #Fact    : 0
% 2.83/1.41  #Define  : 0
% 2.83/1.41  #Split   : 0
% 2.83/1.41  #Chain   : 0
% 2.83/1.41  #Close   : 0
% 2.83/1.41  
% 2.83/1.41  Ordering : KBO
% 2.83/1.41  
% 2.83/1.41  Simplification rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Subsume      : 0
% 2.83/1.41  #Demod        : 211
% 2.83/1.41  #Tautology    : 236
% 2.83/1.41  #SimpNegUnit  : 0
% 2.83/1.41  #BackRed      : 4
% 2.83/1.41  
% 2.83/1.41  #Partial instantiations: 0
% 2.83/1.41  #Strategies tried      : 1
% 2.83/1.41  
% 2.83/1.41  Timing (in seconds)
% 2.83/1.41  ----------------------
% 2.83/1.41  Preprocessing        : 0.27
% 2.83/1.42  Parsing              : 0.16
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.38
% 2.83/1.42  Inferencing          : 0.13
% 2.83/1.42  Reduction            : 0.16
% 2.83/1.42  Demodulation         : 0.13
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.05
% 2.83/1.42  Abstraction          : 0.02
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.68
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
