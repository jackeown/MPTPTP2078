%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 117 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_20,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(B_19,A_20)
      | ~ r1_xboole_0(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_297,plain,(
    ! [A_43,B_44,C_45] :
      ( k3_xboole_0(A_43,k2_xboole_0(B_44,C_45)) = k3_xboole_0(A_43,C_45)
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_335,plain,(
    ! [A_43,A_1,B_2] :
      ( k3_xboole_0(A_43,k2_xboole_0(A_1,B_2)) = k3_xboole_0(A_43,A_1)
      | ~ r1_xboole_0(A_43,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_18,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_25])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k3_xboole_0(A_14,k2_xboole_0(B_15,C_16)) = k3_xboole_0(A_14,C_16)
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,C_32)
      | ~ r1_xboole_0(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [A_34] :
      ( r1_xboole_0(A_34,'#skF_4')
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_27,B_28] :
      ( ~ r1_xboole_0(k3_xboole_0(A_27,B_28),B_28)
      | r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [B_4,A_3] :
      ( ~ r1_xboole_0(k3_xboole_0(B_4,A_3),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_467,plain,(
    ! [A_55] :
      ( r1_xboole_0(A_55,'#skF_4')
      | ~ r1_tarski(k3_xboole_0('#skF_4',A_55),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_162,c_132])).

tff(c_1569,plain,(
    ! [B_140,C_141] :
      ( r1_xboole_0(k2_xboole_0(B_140,C_141),'#skF_4')
      | ~ r1_tarski(k3_xboole_0('#skF_4',C_141),'#skF_3')
      | ~ r1_xboole_0('#skF_4',B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_467])).

tff(c_16,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_1574,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')),'#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1569,c_23])).

tff(c_1586,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1574])).

tff(c_1590,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_1'),'#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_1586])).

tff(c_1595,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_1590])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_25])).

tff(c_656,plain,(
    ! [A_67,A_68,B_69] :
      ( k3_xboole_0(A_67,k2_xboole_0(A_68,B_69)) = k3_xboole_0(A_67,A_68)
      | ~ r1_xboole_0(A_67,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_2096,plain,(
    ! [A_170,B_171,A_172] :
      ( k3_xboole_0(A_170,B_171) = k3_xboole_0(A_170,A_172)
      | ~ r1_xboole_0(A_170,A_172)
      | ~ r1_xboole_0(A_170,B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_14])).

tff(c_2264,plain,(
    ! [B_173] :
      ( k3_xboole_0('#skF_4',B_173) = k3_xboole_0('#skF_4','#skF_1')
      | ~ r1_xboole_0('#skF_4',B_173) ) ),
    inference(resolution,[status(thm)],[c_34,c_2096])).

tff(c_2374,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k3_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2264])).

tff(c_80,plain,(
    ! [B_23,A_24] : k3_xboole_0(B_23,A_24) = k3_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [B_23,A_24] : r1_tarski(k3_xboole_0(B_23,A_24),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_2655,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2374,c_95])).

tff(c_2677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1595,c_2655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:14:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.80  
% 4.43/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.80  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.43/1.80  
% 4.43/1.80  %Foreground sorts:
% 4.43/1.80  
% 4.43/1.80  
% 4.43/1.80  %Background operators:
% 4.43/1.80  
% 4.43/1.80  
% 4.43/1.80  %Foreground operators:
% 4.43/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.80  
% 4.43/1.81  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 4.43/1.81  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.43/1.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.43/1.81  tff(f_51, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.43/1.81  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.43/1.81  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.43/1.81  tff(f_47, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.43/1.81  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.43/1.81  tff(c_20, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.81  tff(c_25, plain, (![B_19, A_20]: (r1_xboole_0(B_19, A_20) | ~r1_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.43/1.81  tff(c_33, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_25])).
% 4.43/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.43/1.81  tff(c_297, plain, (![A_43, B_44, C_45]: (k3_xboole_0(A_43, k2_xboole_0(B_44, C_45))=k3_xboole_0(A_43, C_45) | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.81  tff(c_335, plain, (![A_43, A_1, B_2]: (k3_xboole_0(A_43, k2_xboole_0(A_1, B_2))=k3_xboole_0(A_43, A_1) | ~r1_xboole_0(A_43, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_297])).
% 4.43/1.81  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.81  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_25])).
% 4.43/1.81  tff(c_14, plain, (![A_14, B_15, C_16]: (k3_xboole_0(A_14, k2_xboole_0(B_15, C_16))=k3_xboole_0(A_14, C_16) | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.81  tff(c_143, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, C_32) | ~r1_xboole_0(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.43/1.81  tff(c_162, plain, (![A_34]: (r1_xboole_0(A_34, '#skF_4') | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_143])).
% 4.43/1.81  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.81  tff(c_129, plain, (![A_27, B_28]: (~r1_xboole_0(k3_xboole_0(A_27, B_28), B_28) | r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.43/1.81  tff(c_132, plain, (![B_4, A_3]: (~r1_xboole_0(k3_xboole_0(B_4, A_3), B_4) | r1_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_129])).
% 4.43/1.81  tff(c_467, plain, (![A_55]: (r1_xboole_0(A_55, '#skF_4') | ~r1_tarski(k3_xboole_0('#skF_4', A_55), '#skF_3'))), inference(resolution, [status(thm)], [c_162, c_132])).
% 4.43/1.81  tff(c_1569, plain, (![B_140, C_141]: (r1_xboole_0(k2_xboole_0(B_140, C_141), '#skF_4') | ~r1_tarski(k3_xboole_0('#skF_4', C_141), '#skF_3') | ~r1_xboole_0('#skF_4', B_140))), inference(superposition, [status(thm), theory('equality')], [c_14, c_467])).
% 4.43/1.81  tff(c_16, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.81  tff(c_23, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 4.43/1.81  tff(c_1574, plain, (~r1_tarski(k3_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2')), '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1569, c_23])).
% 4.43/1.81  tff(c_1586, plain, (~r1_tarski(k3_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1574])).
% 4.43/1.81  tff(c_1590, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_1'), '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_1586])).
% 4.43/1.81  tff(c_1595, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_1590])).
% 4.43/1.81  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.81  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_25])).
% 4.43/1.81  tff(c_656, plain, (![A_67, A_68, B_69]: (k3_xboole_0(A_67, k2_xboole_0(A_68, B_69))=k3_xboole_0(A_67, A_68) | ~r1_xboole_0(A_67, B_69))), inference(superposition, [status(thm), theory('equality')], [c_2, c_297])).
% 4.43/1.81  tff(c_2096, plain, (![A_170, B_171, A_172]: (k3_xboole_0(A_170, B_171)=k3_xboole_0(A_170, A_172) | ~r1_xboole_0(A_170, A_172) | ~r1_xboole_0(A_170, B_171))), inference(superposition, [status(thm), theory('equality')], [c_656, c_14])).
% 4.43/1.81  tff(c_2264, plain, (![B_173]: (k3_xboole_0('#skF_4', B_173)=k3_xboole_0('#skF_4', '#skF_1') | ~r1_xboole_0('#skF_4', B_173))), inference(resolution, [status(thm)], [c_34, c_2096])).
% 4.43/1.81  tff(c_2374, plain, (k3_xboole_0('#skF_4', '#skF_3')=k3_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_2264])).
% 4.43/1.81  tff(c_80, plain, (![B_23, A_24]: (k3_xboole_0(B_23, A_24)=k3_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.81  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.81  tff(c_95, plain, (![B_23, A_24]: (r1_tarski(k3_xboole_0(B_23, A_24), A_24))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 4.43/1.81  tff(c_2655, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_1'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2374, c_95])).
% 4.43/1.81  tff(c_2677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1595, c_2655])).
% 4.43/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.81  
% 4.43/1.81  Inference rules
% 4.43/1.81  ----------------------
% 4.43/1.81  #Ref     : 0
% 4.43/1.81  #Sup     : 735
% 4.43/1.81  #Fact    : 0
% 4.43/1.81  #Define  : 0
% 4.43/1.81  #Split   : 7
% 4.43/1.81  #Chain   : 0
% 4.43/1.81  #Close   : 0
% 4.43/1.81  
% 4.43/1.81  Ordering : KBO
% 4.43/1.81  
% 4.43/1.81  Simplification rules
% 4.43/1.81  ----------------------
% 4.43/1.81  #Subsume      : 266
% 4.43/1.81  #Demod        : 75
% 4.43/1.81  #Tautology    : 65
% 4.43/1.81  #SimpNegUnit  : 1
% 4.43/1.81  #BackRed      : 1
% 4.43/1.81  
% 4.43/1.81  #Partial instantiations: 0
% 4.43/1.81  #Strategies tried      : 1
% 4.43/1.81  
% 4.43/1.81  Timing (in seconds)
% 4.43/1.81  ----------------------
% 4.43/1.81  Preprocessing        : 0.26
% 4.43/1.81  Parsing              : 0.15
% 4.43/1.81  CNF conversion       : 0.02
% 4.43/1.81  Main loop            : 0.78
% 4.43/1.81  Inferencing          : 0.24
% 4.43/1.81  Reduction            : 0.26
% 4.43/1.81  Demodulation         : 0.18
% 4.43/1.81  BG Simplification    : 0.03
% 4.43/1.81  Subsumption          : 0.21
% 4.43/1.81  Abstraction          : 0.03
% 4.43/1.81  MUC search           : 0.00
% 4.43/1.81  Cooper               : 0.00
% 4.43/1.81  Total                : 1.07
% 4.43/1.81  Index Insertion      : 0.00
% 4.43/1.81  Index Deletion       : 0.00
% 4.43/1.81  Index Matching       : 0.00
% 4.43/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
