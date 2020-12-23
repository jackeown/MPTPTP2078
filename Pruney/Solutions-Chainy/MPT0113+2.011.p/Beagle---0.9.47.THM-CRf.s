%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  74 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_57,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [A_37,B_38] : r1_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(B_38,A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_20] :
      ( ~ r1_xboole_0(A_20,A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_22])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_287])).

tff(c_305,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_302])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_145,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_299,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_287])).

tff(c_343,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_299])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_347,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_16])).

tff(c_362,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_347])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_858,plain,(
    ! [C_78] :
      ( r1_tarski('#skF_1',C_78)
      | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_8])).

tff(c_874,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_858])).

tff(c_882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_874])).

tff(c_883,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1400,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_xboole_0(A_107,C_108)
      | ~ r1_xboole_0(B_109,C_108)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1544,plain,(
    ! [A_117,B_118,A_119] :
      ( r1_xboole_0(A_117,B_118)
      | ~ r1_tarski(A_117,k4_xboole_0(A_119,B_118)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1400])).

tff(c_1570,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1544])).

tff(c_1583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_883,c_1570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.49  
% 2.81/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.49  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.81/1.49  
% 2.81/1.49  %Foreground sorts:
% 2.81/1.49  
% 2.81/1.49  
% 2.81/1.49  %Background operators:
% 2.81/1.49  
% 2.81/1.49  
% 2.81/1.49  %Foreground operators:
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.49  
% 2.81/1.50  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.81/1.50  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.81/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.81/1.50  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.81/1.50  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 2.81/1.50  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.81/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.81/1.50  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.81/1.50  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.81/1.50  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.81/1.50  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.81/1.50  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.81/1.50  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.81/1.50  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.50  tff(c_57, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 2.81/1.50  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.50  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.50  tff(c_154, plain, (![A_37, B_38]: (r1_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(B_38, A_37)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.50  tff(c_22, plain, (![A_20]: (~r1_xboole_0(A_20, A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.50  tff(c_159, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_22])).
% 2.81/1.50  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.50  tff(c_287, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.50  tff(c_302, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_287])).
% 2.81/1.50  tff(c_305, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_302])).
% 2.81/1.50  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.50  tff(c_145, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.50  tff(c_152, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_145])).
% 2.81/1.50  tff(c_299, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_152, c_287])).
% 2.81/1.50  tff(c_343, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_305, c_299])).
% 2.81/1.50  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.50  tff(c_347, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_343, c_16])).
% 2.81/1.50  tff(c_362, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_347])).
% 2.81/1.50  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.50  tff(c_858, plain, (![C_78]: (r1_tarski('#skF_1', C_78) | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), C_78))), inference(superposition, [status(thm), theory('equality')], [c_362, c_8])).
% 2.81/1.50  tff(c_874, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_858])).
% 2.81/1.50  tff(c_882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_874])).
% 2.81/1.50  tff(c_883, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.81/1.50  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.50  tff(c_1400, plain, (![A_107, C_108, B_109]: (r1_xboole_0(A_107, C_108) | ~r1_xboole_0(B_109, C_108) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.50  tff(c_1544, plain, (![A_117, B_118, A_119]: (r1_xboole_0(A_117, B_118) | ~r1_tarski(A_117, k4_xboole_0(A_119, B_118)))), inference(resolution, [status(thm)], [c_24, c_1400])).
% 2.81/1.50  tff(c_1570, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1544])).
% 2.81/1.50  tff(c_1583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_883, c_1570])).
% 2.81/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.50  
% 2.81/1.50  Inference rules
% 2.81/1.50  ----------------------
% 2.81/1.50  #Ref     : 0
% 2.81/1.50  #Sup     : 368
% 2.81/1.50  #Fact    : 0
% 2.81/1.50  #Define  : 0
% 2.81/1.50  #Split   : 1
% 2.81/1.50  #Chain   : 0
% 2.81/1.50  #Close   : 0
% 2.81/1.50  
% 2.81/1.50  Ordering : KBO
% 2.81/1.50  
% 2.81/1.50  Simplification rules
% 2.81/1.50  ----------------------
% 2.81/1.50  #Subsume      : 8
% 2.81/1.50  #Demod        : 172
% 2.81/1.50  #Tautology    : 277
% 2.81/1.50  #SimpNegUnit  : 2
% 2.81/1.50  #BackRed      : 1
% 2.81/1.50  
% 2.81/1.50  #Partial instantiations: 0
% 2.81/1.50  #Strategies tried      : 1
% 2.81/1.50  
% 2.81/1.50  Timing (in seconds)
% 2.81/1.50  ----------------------
% 2.81/1.50  Preprocessing        : 0.25
% 2.81/1.50  Parsing              : 0.14
% 2.81/1.51  CNF conversion       : 0.02
% 2.81/1.51  Main loop            : 0.40
% 2.81/1.51  Inferencing          : 0.15
% 2.81/1.51  Reduction            : 0.14
% 2.81/1.51  Demodulation         : 0.11
% 2.81/1.51  BG Simplification    : 0.02
% 2.81/1.51  Subsumption          : 0.06
% 2.81/1.51  Abstraction          : 0.02
% 2.81/1.51  MUC search           : 0.00
% 2.81/1.51  Cooper               : 0.00
% 2.81/1.51  Total                : 0.68
% 2.81/1.51  Index Insertion      : 0.00
% 2.81/1.51  Index Deletion       : 0.00
% 2.81/1.51  Index Matching       : 0.00
% 2.81/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
