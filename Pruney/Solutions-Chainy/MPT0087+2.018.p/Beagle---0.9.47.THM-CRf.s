%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 101 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   39 ( 104 expanded)
%              Number of equality atoms :   27 (  72 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_87,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_87])).

tff(c_113,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_254,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_314,plain,(
    ! [C_38] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_38)) = k4_xboole_0('#skF_1',C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_254])).

tff(c_30,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_45,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_35])).

tff(c_154,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_215,plain,(
    ! [A_34] : k4_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_184])).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = k2_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_6])).

tff(c_191,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_184])).

tff(c_264,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,k4_xboole_0(A_36,B_37))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_191])).

tff(c_331,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(B_37,A_36)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_264])).

tff(c_4570,plain,(
    ! [C_112,A_113,B_114] : k2_xboole_0(C_112,k4_xboole_0(A_113,k2_xboole_0(B_114,C_112))) = k2_xboole_0(C_112,k4_xboole_0(A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_6])).

tff(c_6623,plain,(
    ! [A_135,B_136] : k2_xboole_0(A_135,k4_xboole_0(A_135,B_136)) = k2_xboole_0(A_135,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_4570])).

tff(c_6715,plain,(
    ! [B_136] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_136)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6623,c_314])).

tff(c_6860,plain,(
    ! [B_137] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_137)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_314,c_220,c_6715])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6943,plain,(
    ! [B_137] : r1_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6860,c_16])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6943,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:01:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.97  
% 4.89/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.97  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.89/1.97  
% 4.89/1.97  %Foreground sorts:
% 4.89/1.97  
% 4.89/1.97  
% 4.89/1.97  %Background operators:
% 4.89/1.97  
% 4.89/1.97  
% 4.89/1.97  %Foreground operators:
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.89/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.89/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.89/1.97  
% 4.89/1.98  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.89/1.98  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 4.89/1.98  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.89/1.98  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.89/1.98  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.89/1.98  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.89/1.98  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.89/1.98  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.89/1.98  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.89/1.98  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.89/1.98  tff(c_35, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.89/1.98  tff(c_47, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_35])).
% 4.89/1.98  tff(c_87, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.89/1.98  tff(c_108, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_47, c_87])).
% 4.89/1.98  tff(c_113, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_108])).
% 4.89/1.98  tff(c_254, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.89/1.98  tff(c_314, plain, (![C_38]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_38))=k4_xboole_0('#skF_1', C_38))), inference(superposition, [status(thm), theory('equality')], [c_113, c_254])).
% 4.89/1.98  tff(c_30, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.89/1.98  tff(c_33, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_30])).
% 4.89/1.98  tff(c_45, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_35])).
% 4.89/1.98  tff(c_154, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.89/1.98  tff(c_184, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_154])).
% 4.89/1.98  tff(c_215, plain, (![A_34]: (k4_xboole_0(A_34, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_184])).
% 4.89/1.98  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.89/1.98  tff(c_220, plain, (![A_34]: (k2_xboole_0(A_34, k1_xboole_0)=k2_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_215, c_6])).
% 4.89/1.98  tff(c_191, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_184])).
% 4.89/1.98  tff(c_264, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, k4_xboole_0(A_36, B_37)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_254, c_191])).
% 4.89/1.98  tff(c_331, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(B_37, A_36))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_264])).
% 4.89/1.98  tff(c_4570, plain, (![C_112, A_113, B_114]: (k2_xboole_0(C_112, k4_xboole_0(A_113, k2_xboole_0(B_114, C_112)))=k2_xboole_0(C_112, k4_xboole_0(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_6])).
% 4.89/1.98  tff(c_6623, plain, (![A_135, B_136]: (k2_xboole_0(A_135, k4_xboole_0(A_135, B_136))=k2_xboole_0(A_135, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_4570])).
% 4.89/1.98  tff(c_6715, plain, (![B_136]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_136))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6623, c_314])).
% 4.89/1.98  tff(c_6860, plain, (![B_137]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_137))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_314, c_220, c_6715])).
% 4.89/1.98  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.89/1.98  tff(c_6943, plain, (![B_137]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_137)))), inference(superposition, [status(thm), theory('equality')], [c_6860, c_16])).
% 4.89/1.98  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.89/1.98  tff(c_7021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6943, c_18])).
% 4.89/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.98  
% 4.89/1.98  Inference rules
% 4.89/1.98  ----------------------
% 4.89/1.98  #Ref     : 0
% 4.89/1.98  #Sup     : 1717
% 4.89/1.98  #Fact    : 0
% 4.89/1.98  #Define  : 0
% 4.89/1.98  #Split   : 0
% 4.89/1.98  #Chain   : 0
% 4.89/1.98  #Close   : 0
% 4.89/1.98  
% 4.89/1.98  Ordering : KBO
% 4.89/1.98  
% 4.89/1.98  Simplification rules
% 4.89/1.98  ----------------------
% 4.89/1.98  #Subsume      : 11
% 4.89/1.98  #Demod        : 1619
% 4.89/1.98  #Tautology    : 1088
% 4.89/1.98  #SimpNegUnit  : 0
% 4.89/1.98  #BackRed      : 4
% 4.89/1.98  
% 4.89/1.98  #Partial instantiations: 0
% 4.89/1.98  #Strategies tried      : 1
% 4.89/1.98  
% 4.89/1.98  Timing (in seconds)
% 4.89/1.98  ----------------------
% 4.89/1.98  Preprocessing        : 0.25
% 4.89/1.98  Parsing              : 0.14
% 4.89/1.98  CNF conversion       : 0.02
% 4.89/1.98  Main loop            : 0.99
% 4.89/1.98  Inferencing          : 0.30
% 4.89/1.98  Reduction            : 0.44
% 4.89/1.98  Demodulation         : 0.36
% 4.89/1.98  BG Simplification    : 0.03
% 4.89/1.98  Subsumption          : 0.15
% 4.89/1.98  Abstraction          : 0.05
% 4.89/1.98  MUC search           : 0.00
% 4.89/1.98  Cooper               : 0.00
% 4.89/1.98  Total                : 1.26
% 4.89/1.98  Index Insertion      : 0.00
% 4.89/1.98  Index Deletion       : 0.00
% 4.89/1.98  Index Matching       : 0.00
% 4.89/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
