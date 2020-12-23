%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :   53 (  88 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  95 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_231,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_238,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_231])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_513,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1623,plain,(
    ! [A_71,B_72] : k2_xboole_0(k3_xboole_0(A_71,B_72),k4_xboole_0(B_72,A_71)) = B_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_513])).

tff(c_1706,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_1623])).

tff(c_178,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_1767,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1706,c_200])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k2_xboole_0(B_44,A_43)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_22])).

tff(c_454,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_426])).

tff(c_1476,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k4_xboole_0(A_68,B_69),C_70) = k4_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7014,plain,(
    ! [C_131,A_132,B_133] : k2_xboole_0(C_131,k4_xboole_0(A_132,k2_xboole_0(B_133,C_131))) = k2_xboole_0(C_131,k4_xboole_0(A_132,B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1476,c_16])).

tff(c_7222,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_7014])).

tff(c_7320,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_10,c_7222])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_558,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_513])).

tff(c_972,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_200])).

tff(c_193,plain,(
    ! [A_33,B_32] : k4_xboole_0(A_33,k2_xboole_0(B_32,A_33)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_22])).

tff(c_7892,plain,(
    ! [A_137] : k2_xboole_0('#skF_2',k4_xboole_0(A_137,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_137,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_7014])).

tff(c_8008,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_7892])).

tff(c_8054,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7320,c_2,c_972,c_10,c_8008])).

tff(c_8056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_8054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.57  
% 5.91/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.57  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.91/2.57  
% 5.91/2.57  %Foreground sorts:
% 5.91/2.57  
% 5.91/2.57  
% 5.91/2.57  %Background operators:
% 5.91/2.57  
% 5.91/2.57  
% 5.91/2.57  %Foreground operators:
% 5.91/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.91/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.91/2.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.91/2.57  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.57  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.57  tff('#skF_1', type, '#skF_1': $i).
% 5.91/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.57  tff('#skF_4', type, '#skF_4': $i).
% 5.91/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.91/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.91/2.57  
% 5.91/2.58  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 5.91/2.58  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.91/2.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.91/2.58  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.91/2.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.91/2.58  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.91/2.58  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.91/2.58  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.91/2.58  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.91/2.58  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.91/2.58  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.91/2.58  tff(c_231, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.91/2.58  tff(c_238, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_231])).
% 5.91/2.58  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.91/2.58  tff(c_513, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.91/2.58  tff(c_1623, plain, (![A_71, B_72]: (k2_xboole_0(k3_xboole_0(A_71, B_72), k4_xboole_0(B_72, A_71))=B_72)), inference(superposition, [status(thm), theory('equality')], [c_4, c_513])).
% 5.91/2.58  tff(c_1706, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_238, c_1623])).
% 5.91/2.58  tff(c_178, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.91/2.58  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.91/2.58  tff(c_200, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 5.91/2.58  tff(c_1767, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1706, c_200])).
% 5.91/2.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.91/2.58  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.91/2.58  tff(c_35, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 5.91/2.58  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.91/2.58  tff(c_426, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k2_xboole_0(B_44, A_43))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_22])).
% 5.91/2.58  tff(c_454, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35, c_426])).
% 5.91/2.58  tff(c_1476, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k4_xboole_0(A_68, B_69), C_70)=k4_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.91/2.58  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.91/2.58  tff(c_7014, plain, (![C_131, A_132, B_133]: (k2_xboole_0(C_131, k4_xboole_0(A_132, k2_xboole_0(B_133, C_131)))=k2_xboole_0(C_131, k4_xboole_0(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_1476, c_16])).
% 5.91/2.58  tff(c_7222, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_454, c_7014])).
% 5.91/2.58  tff(c_7320, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_10, c_7222])).
% 5.91/2.58  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.91/2.58  tff(c_239, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_231])).
% 5.91/2.58  tff(c_558, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_239, c_513])).
% 5.91/2.58  tff(c_972, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_558, c_200])).
% 5.91/2.58  tff(c_193, plain, (![A_33, B_32]: (k4_xboole_0(A_33, k2_xboole_0(B_32, A_33))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_22])).
% 5.91/2.58  tff(c_7892, plain, (![A_137]: (k2_xboole_0('#skF_2', k4_xboole_0(A_137, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_137, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35, c_7014])).
% 5.91/2.58  tff(c_8008, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_7892])).
% 5.91/2.58  tff(c_8054, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7320, c_2, c_972, c_10, c_8008])).
% 5.91/2.58  tff(c_8056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_8054])).
% 5.91/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.58  
% 5.91/2.58  Inference rules
% 5.91/2.58  ----------------------
% 5.91/2.58  #Ref     : 1
% 5.91/2.58  #Sup     : 2039
% 5.91/2.58  #Fact    : 0
% 5.91/2.58  #Define  : 0
% 5.91/2.58  #Split   : 0
% 5.91/2.58  #Chain   : 0
% 5.91/2.58  #Close   : 0
% 5.91/2.59  
% 5.91/2.59  Ordering : KBO
% 5.91/2.59  
% 5.91/2.59  Simplification rules
% 5.91/2.59  ----------------------
% 5.91/2.59  #Subsume      : 7
% 5.91/2.59  #Demod        : 2144
% 5.91/2.59  #Tautology    : 1437
% 5.91/2.59  #SimpNegUnit  : 3
% 5.91/2.59  #BackRed      : 6
% 5.91/2.59  
% 5.91/2.59  #Partial instantiations: 0
% 5.91/2.59  #Strategies tried      : 1
% 5.91/2.59  
% 5.91/2.59  Timing (in seconds)
% 5.91/2.59  ----------------------
% 6.25/2.59  Preprocessing        : 0.36
% 6.25/2.59  Parsing              : 0.19
% 6.25/2.59  CNF conversion       : 0.02
% 6.25/2.59  Main loop            : 1.38
% 6.25/2.59  Inferencing          : 0.36
% 6.25/2.59  Reduction            : 0.72
% 6.25/2.59  Demodulation         : 0.62
% 6.25/2.59  BG Simplification    : 0.04
% 6.25/2.59  Subsumption          : 0.19
% 6.25/2.59  Abstraction          : 0.06
% 6.25/2.59  MUC search           : 0.00
% 6.25/2.59  Cooper               : 0.00
% 6.25/2.59  Total                : 1.77
% 6.25/2.59  Index Insertion      : 0.00
% 6.25/2.59  Index Deletion       : 0.00
% 6.25/2.59  Index Matching       : 0.00
% 6.25/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
