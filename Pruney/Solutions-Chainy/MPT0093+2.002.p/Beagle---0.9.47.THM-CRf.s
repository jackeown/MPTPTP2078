%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.96s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 231 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :   57 ( 288 expanded)
%              Number of equality atoms :   45 ( 185 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_121,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [B_33,A_34,C_35] : k4_xboole_0(k3_xboole_0(B_33,A_34),C_35) = k3_xboole_0(A_34,k4_xboole_0(B_33,C_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_488,plain,(
    ! [C_37] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_37)) = k4_xboole_0('#skF_1',C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_346])).

tff(c_528,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_488])).

tff(c_542,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_528])).

tff(c_118,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_434,plain,(
    ! [C_36] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_36)) = k4_xboole_0('#skF_1',C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_146])).

tff(c_458,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k1_xboole_0)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_434])).

tff(c_470,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_458])).

tff(c_544,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_470])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_97])).

tff(c_208,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_118])).

tff(c_559,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_208])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_211,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_10])).

tff(c_574,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_211])).

tff(c_576,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_574])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k3_xboole_0(A_8,B_9),C_10) = k3_xboole_0(A_8,k4_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_593,plain,(
    ! [C_10] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_10)) = k4_xboole_0('#skF_1',C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_12])).

tff(c_617,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_699,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_617])).

tff(c_3035,plain,(
    ! [B_69,A_70,C_71] : k3_xboole_0(B_69,k4_xboole_0(A_70,C_71)) = k3_xboole_0(A_70,k4_xboole_0(B_69,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_12])).

tff(c_3458,plain,(
    ! [B_72] : k3_xboole_0('#skF_1',k4_xboole_0(B_72,'#skF_3')) = k3_xboole_0(B_72,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_3035])).

tff(c_106,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_3500,plain,(
    ! [B_72] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k4_xboole_0(B_72,'#skF_3'))) = k4_xboole_0('#skF_1',k3_xboole_0(B_72,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3458,c_106])).

tff(c_8121,plain,(
    ! [B_107] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k4_xboole_0(B_107,'#skF_3'))) = k4_xboole_0('#skF_1',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_699,c_3500])).

tff(c_8173,plain,(
    ! [B_107] : k4_xboole_0('#skF_1',k4_xboole_0(B_107,'#skF_3')) = k4_xboole_0('#skF_1',B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_8121])).

tff(c_75,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_18])).

tff(c_8913,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8173,c_83])).

tff(c_8917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/4.07  
% 10.57/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/4.07  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.57/4.07  
% 10.57/4.07  %Foreground sorts:
% 10.57/4.07  
% 10.57/4.07  
% 10.57/4.07  %Background operators:
% 10.57/4.07  
% 10.57/4.07  
% 10.57/4.07  %Foreground operators:
% 10.57/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.57/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.57/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.57/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.57/4.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.57/4.07  tff('#skF_2', type, '#skF_2': $i).
% 10.57/4.07  tff('#skF_3', type, '#skF_3': $i).
% 10.57/4.07  tff('#skF_1', type, '#skF_1': $i).
% 10.57/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.57/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.57/4.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.57/4.07  
% 10.96/4.09  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 10.96/4.09  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.96/4.09  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.96/4.09  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.96/4.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.96/4.09  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.96/4.09  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.96/4.09  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.96/4.09  tff(c_66, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.96/4.09  tff(c_70, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_66])).
% 10.96/4.09  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.96/4.09  tff(c_97, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.96/4.09  tff(c_115, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_97])).
% 10.96/4.09  tff(c_121, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_115])).
% 10.96/4.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.96/4.09  tff(c_146, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.09  tff(c_346, plain, (![B_33, A_34, C_35]: (k4_xboole_0(k3_xboole_0(B_33, A_34), C_35)=k3_xboole_0(A_34, k4_xboole_0(B_33, C_35)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 10.96/4.09  tff(c_488, plain, (![C_37]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_37))=k4_xboole_0('#skF_1', C_37))), inference(superposition, [status(thm), theory('equality')], [c_121, c_346])).
% 10.96/4.09  tff(c_528, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_488])).
% 10.96/4.09  tff(c_542, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_528])).
% 10.96/4.09  tff(c_118, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_97])).
% 10.96/4.09  tff(c_434, plain, (![C_36]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_36))=k4_xboole_0('#skF_1', C_36))), inference(superposition, [status(thm), theory('equality')], [c_121, c_146])).
% 10.96/4.09  tff(c_458, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k1_xboole_0))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_434])).
% 10.96/4.09  tff(c_470, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_458])).
% 10.96/4.09  tff(c_544, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_542, c_470])).
% 10.96/4.09  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.96/4.09  tff(c_84, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.96/4.09  tff(c_92, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_84])).
% 10.96/4.09  tff(c_112, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_97])).
% 10.96/4.09  tff(c_208, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_118])).
% 10.96/4.09  tff(c_559, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_544, c_208])).
% 10.96/4.09  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.96/4.09  tff(c_211, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_10])).
% 10.96/4.09  tff(c_574, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_211])).
% 10.96/4.09  tff(c_576, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_574])).
% 10.96/4.09  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k3_xboole_0(A_8, B_9), C_10)=k3_xboole_0(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.09  tff(c_593, plain, (![C_10]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_10))=k4_xboole_0('#skF_1', C_10))), inference(superposition, [status(thm), theory('equality')], [c_576, c_12])).
% 10.96/4.09  tff(c_617, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 10.96/4.09  tff(c_699, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_617])).
% 10.96/4.09  tff(c_3035, plain, (![B_69, A_70, C_71]: (k3_xboole_0(B_69, k4_xboole_0(A_70, C_71))=k3_xboole_0(A_70, k4_xboole_0(B_69, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_346, c_12])).
% 10.96/4.09  tff(c_3458, plain, (![B_72]: (k3_xboole_0('#skF_1', k4_xboole_0(B_72, '#skF_3'))=k3_xboole_0(B_72, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_3035])).
% 10.96/4.09  tff(c_106, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k3_xboole_0(A_6, k4_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 10.96/4.09  tff(c_3500, plain, (![B_72]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k4_xboole_0(B_72, '#skF_3')))=k4_xboole_0('#skF_1', k3_xboole_0(B_72, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3458, c_106])).
% 10.96/4.09  tff(c_8121, plain, (![B_107]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k4_xboole_0(B_107, '#skF_3')))=k4_xboole_0('#skF_1', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_699, c_3500])).
% 10.96/4.09  tff(c_8173, plain, (![B_107]: (k4_xboole_0('#skF_1', k4_xboole_0(B_107, '#skF_3'))=k4_xboole_0('#skF_1', B_107))), inference(superposition, [status(thm), theory('equality')], [c_593, c_8121])).
% 10.96/4.09  tff(c_75, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | k4_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.96/4.09  tff(c_18, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.96/4.09  tff(c_83, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_18])).
% 10.96/4.09  tff(c_8913, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8173, c_83])).
% 10.96/4.09  tff(c_8917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_8913])).
% 10.96/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.96/4.09  
% 10.96/4.09  Inference rules
% 10.96/4.09  ----------------------
% 10.96/4.09  #Ref     : 0
% 10.96/4.09  #Sup     : 2130
% 10.96/4.09  #Fact    : 0
% 10.96/4.09  #Define  : 0
% 10.96/4.09  #Split   : 0
% 10.96/4.09  #Chain   : 0
% 10.96/4.09  #Close   : 0
% 10.96/4.09  
% 10.96/4.09  Ordering : KBO
% 10.96/4.09  
% 10.96/4.09  Simplification rules
% 10.96/4.09  ----------------------
% 10.96/4.09  #Subsume      : 42
% 10.96/4.09  #Demod        : 3733
% 10.96/4.09  #Tautology    : 1313
% 10.96/4.09  #SimpNegUnit  : 0
% 10.96/4.09  #BackRed      : 23
% 10.96/4.09  
% 10.96/4.09  #Partial instantiations: 0
% 10.96/4.09  #Strategies tried      : 1
% 10.96/4.09  
% 10.96/4.09  Timing (in seconds)
% 10.96/4.09  ----------------------
% 10.96/4.10  Preprocessing        : 0.42
% 10.96/4.10  Parsing              : 0.22
% 10.96/4.10  CNF conversion       : 0.03
% 10.96/4.10  Main loop            : 2.79
% 10.96/4.10  Inferencing          : 0.66
% 10.96/4.10  Reduction            : 1.66
% 10.96/4.10  Demodulation         : 1.49
% 10.96/4.10  BG Simplification    : 0.08
% 10.96/4.10  Subsumption          : 0.29
% 10.96/4.10  Abstraction          : 0.12
% 10.96/4.10  MUC search           : 0.00
% 10.96/4.10  Cooper               : 0.00
% 10.96/4.10  Total                : 3.26
% 10.96/4.10  Index Insertion      : 0.00
% 10.96/4.10  Index Deletion       : 0.00
% 10.96/4.10  Index Matching       : 0.00
% 10.96/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
