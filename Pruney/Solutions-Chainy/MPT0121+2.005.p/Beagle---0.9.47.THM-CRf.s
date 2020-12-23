%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_110,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( k3_xboole_0(A_17,k2_xboole_0(B_18,C_19)) = k3_xboole_0(A_17,C_19)
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,C_35)
      | ~ r1_xboole_0(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    ! [A_34] :
      ( r1_xboole_0(A_34,'#skF_4')
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_338,plain,(
    ! [A_55,B_56,C_57] :
      ( k3_xboole_0(A_55,k2_xboole_0(B_56,C_57)) = k3_xboole_0(A_55,C_57)
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_26,B_27] :
      ( ~ r1_xboole_0(k3_xboole_0(A_26,B_27),B_27)
      | r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_1960,plain,(
    ! [A_182,C_183,B_184] :
      ( ~ r1_xboole_0(k3_xboole_0(A_182,C_183),A_182)
      | r1_xboole_0(k2_xboole_0(B_184,C_183),A_182)
      | ~ r1_xboole_0(A_182,B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_85])).

tff(c_2113,plain,(
    ! [B_189,C_190] :
      ( r1_xboole_0(k2_xboole_0(B_189,C_190),'#skF_4')
      | ~ r1_xboole_0('#skF_4',B_189)
      | ~ r1_tarski(k3_xboole_0('#skF_4',C_190),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_140,c_1960])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_xboole_0(A_9,B_10),C_11) = k2_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_25,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_2118,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2113,c_25])).

tff(c_2127,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2118])).

tff(c_2131,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2127])).

tff(c_2134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_110,c_2131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.74  
% 4.03/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.74  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.03/1.74  
% 4.03/1.74  %Foreground sorts:
% 4.03/1.74  
% 4.03/1.74  
% 4.03/1.74  %Background operators:
% 4.03/1.74  
% 4.03/1.74  
% 4.03/1.74  %Foreground operators:
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.03/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.03/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.03/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.03/1.74  
% 4.03/1.75  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 4.03/1.75  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.03/1.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.03/1.75  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.03/1.75  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.03/1.75  tff(f_53, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.03/1.75  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.03/1.75  tff(f_49, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.03/1.75  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.03/1.75  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.75  tff(c_27, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.03/1.75  tff(c_35, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_27])).
% 4.03/1.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.03/1.75  tff(c_89, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.75  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.75  tff(c_107, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 4.03/1.75  tff(c_110, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 4.03/1.75  tff(c_16, plain, (![A_17, B_18, C_19]: (k3_xboole_0(A_17, k2_xboole_0(B_18, C_19))=k3_xboole_0(A_17, C_19) | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.03/1.75  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.75  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_27])).
% 4.03/1.75  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.75  tff(c_124, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, C_35) | ~r1_xboole_0(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.75  tff(c_140, plain, (![A_34]: (r1_xboole_0(A_34, '#skF_4') | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_124])).
% 4.03/1.75  tff(c_338, plain, (![A_55, B_56, C_57]: (k3_xboole_0(A_55, k2_xboole_0(B_56, C_57))=k3_xboole_0(A_55, C_57) | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.03/1.75  tff(c_82, plain, (![A_26, B_27]: (~r1_xboole_0(k3_xboole_0(A_26, B_27), B_27) | r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.03/1.75  tff(c_85, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 4.03/1.75  tff(c_1960, plain, (![A_182, C_183, B_184]: (~r1_xboole_0(k3_xboole_0(A_182, C_183), A_182) | r1_xboole_0(k2_xboole_0(B_184, C_183), A_182) | ~r1_xboole_0(A_182, B_184))), inference(superposition, [status(thm), theory('equality')], [c_338, c_85])).
% 4.03/1.75  tff(c_2113, plain, (![B_189, C_190]: (r1_xboole_0(k2_xboole_0(B_189, C_190), '#skF_4') | ~r1_xboole_0('#skF_4', B_189) | ~r1_tarski(k3_xboole_0('#skF_4', C_190), '#skF_3'))), inference(resolution, [status(thm)], [c_140, c_1960])).
% 4.03/1.75  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_xboole_0(A_9, B_10), C_11)=k2_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.75  tff(c_18, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.75  tff(c_25, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 4.03/1.75  tff(c_2118, plain, (~r1_xboole_0('#skF_4', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_2113, c_25])).
% 4.03/1.75  tff(c_2127, plain, (~r1_tarski(k3_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2118])).
% 4.03/1.75  tff(c_2131, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2127])).
% 4.03/1.75  tff(c_2134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_110, c_2131])).
% 4.03/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.75  
% 4.03/1.75  Inference rules
% 4.03/1.75  ----------------------
% 4.03/1.75  #Ref     : 0
% 4.03/1.75  #Sup     : 575
% 4.03/1.75  #Fact    : 0
% 4.03/1.75  #Define  : 0
% 4.03/1.75  #Split   : 6
% 4.03/1.75  #Chain   : 0
% 4.03/1.75  #Close   : 0
% 4.03/1.75  
% 4.03/1.75  Ordering : KBO
% 4.03/1.75  
% 4.03/1.75  Simplification rules
% 4.03/1.75  ----------------------
% 4.03/1.75  #Subsume      : 211
% 4.03/1.75  #Demod        : 50
% 4.03/1.75  #Tautology    : 58
% 4.03/1.75  #SimpNegUnit  : 0
% 4.03/1.75  #BackRed      : 0
% 4.03/1.75  
% 4.03/1.75  #Partial instantiations: 0
% 4.03/1.75  #Strategies tried      : 1
% 4.03/1.75  
% 4.03/1.75  Timing (in seconds)
% 4.03/1.75  ----------------------
% 4.03/1.75  Preprocessing        : 0.28
% 4.03/1.75  Parsing              : 0.16
% 4.03/1.75  CNF conversion       : 0.02
% 4.03/1.75  Main loop            : 0.71
% 4.03/1.75  Inferencing          : 0.24
% 4.03/1.75  Reduction            : 0.21
% 4.03/1.75  Demodulation         : 0.15
% 4.03/1.75  BG Simplification    : 0.02
% 4.03/1.75  Subsumption          : 0.19
% 4.03/1.75  Abstraction          : 0.03
% 4.03/1.75  MUC search           : 0.00
% 4.03/1.75  Cooper               : 0.00
% 4.03/1.75  Total                : 1.01
% 4.03/1.75  Index Insertion      : 0.00
% 4.03/1.75  Index Deletion       : 0.00
% 4.03/1.75  Index Matching       : 0.00
% 4.03/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
