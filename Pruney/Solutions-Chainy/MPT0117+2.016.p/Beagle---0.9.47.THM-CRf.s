%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 8.57s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  73 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_217,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k5_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_232,plain,(
    ! [A_46,B_47] : r1_tarski(k5_xboole_0(A_46,B_47),k2_xboole_0(A_46,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_24])).

tff(c_16,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_256,plain,(
    ! [A_48,B_49] : r1_tarski(k5_xboole_0(A_48,B_49),k2_xboole_0(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_273,plain,(
    ! [A_18,B_19] : r1_tarski(k2_xboole_0(A_18,B_19),k2_xboole_0(A_18,k4_xboole_0(B_19,A_18))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski(k4_xboole_0(A_12,B_13),C_14)
      | ~ r1_tarski(A_12,k2_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_541,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,A_62)
      | ~ r1_tarski(A_61,k4_xboole_0(A_62,B_63)) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_7585,plain,(
    ! [A_199,B_200,A_201,B_202] :
      ( r1_tarski(k4_xboole_0(A_199,B_200),A_201)
      | ~ r1_tarski(A_199,k2_xboole_0(B_200,k4_xboole_0(A_201,B_202))) ) ),
    inference(resolution,[status(thm)],[c_12,c_541])).

tff(c_7745,plain,(
    ! [A_203,B_204] : r1_tarski(k4_xboole_0(k2_xboole_0(A_203,B_204),A_203),B_204) ),
    inference(resolution,[status(thm)],[c_273,c_7585])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,'#skF_2')
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_106,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,k2_xboole_0(B_36,C_37))
      | ~ r1_tarski(k4_xboole_0(A_35,B_36),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,k2_xboole_0(B_36,'#skF_2'))
      | ~ r1_tarski(k4_xboole_0(A_35,B_36),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_106])).

tff(c_8433,plain,(
    ! [A_206] : r1_tarski(k2_xboole_0(A_206,'#skF_3'),k2_xboole_0(A_206,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_7745,c_119])).

tff(c_8605,plain,(
    r1_tarski(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8433])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13535,plain,(
    ! [A_271] :
      ( r1_tarski(A_271,'#skF_2')
      | ~ r1_tarski(A_271,k2_xboole_0('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8605,c_8])).

tff(c_13591,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_13535])).

tff(c_13624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_13591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:55:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.57/3.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.20  
% 8.57/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.20  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 8.57/3.20  
% 8.57/3.20  %Foreground sorts:
% 8.57/3.20  
% 8.57/3.20  
% 8.57/3.20  %Background operators:
% 8.57/3.20  
% 8.57/3.20  
% 8.57/3.20  %Foreground operators:
% 8.57/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.57/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.57/3.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.57/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.57/3.20  tff('#skF_2', type, '#skF_2': $i).
% 8.57/3.20  tff('#skF_3', type, '#skF_3': $i).
% 8.57/3.20  tff('#skF_1', type, '#skF_1': $i).
% 8.57/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.57/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.57/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.57/3.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.57/3.20  
% 8.61/3.21  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 8.61/3.21  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.61/3.21  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.61/3.21  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.61/3.21  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.61/3.21  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.61/3.21  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.61/3.21  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.61/3.21  tff(c_18, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.61/3.21  tff(c_217, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k5_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.61/3.21  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.61/3.21  tff(c_232, plain, (![A_46, B_47]: (r1_tarski(k5_xboole_0(A_46, B_47), k2_xboole_0(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 8.61/3.21  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.61/3.21  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.61/3.21  tff(c_36, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_24])).
% 8.61/3.21  tff(c_16, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.61/3.21  tff(c_256, plain, (![A_48, B_49]: (r1_tarski(k5_xboole_0(A_48, B_49), k2_xboole_0(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 8.61/3.21  tff(c_273, plain, (![A_18, B_19]: (r1_tarski(k2_xboole_0(A_18, B_19), k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_256])).
% 8.61/3.21  tff(c_12, plain, (![A_12, B_13, C_14]: (r1_tarski(k4_xboole_0(A_12, B_13), C_14) | ~r1_tarski(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.61/3.21  tff(c_72, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.61/3.21  tff(c_541, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, A_62) | ~r1_tarski(A_61, k4_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_10, c_72])).
% 8.61/3.21  tff(c_7585, plain, (![A_199, B_200, A_201, B_202]: (r1_tarski(k4_xboole_0(A_199, B_200), A_201) | ~r1_tarski(A_199, k2_xboole_0(B_200, k4_xboole_0(A_201, B_202))))), inference(resolution, [status(thm)], [c_12, c_541])).
% 8.61/3.21  tff(c_7745, plain, (![A_203, B_204]: (r1_tarski(k4_xboole_0(k2_xboole_0(A_203, B_204), A_203), B_204))), inference(resolution, [status(thm)], [c_273, c_7585])).
% 8.61/3.21  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.61/3.21  tff(c_80, plain, (![A_30]: (r1_tarski(A_30, '#skF_2') | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_72])).
% 8.61/3.21  tff(c_106, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, k2_xboole_0(B_36, C_37)) | ~r1_tarski(k4_xboole_0(A_35, B_36), C_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.61/3.21  tff(c_119, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(B_36, '#skF_2')) | ~r1_tarski(k4_xboole_0(A_35, B_36), '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_106])).
% 8.61/3.21  tff(c_8433, plain, (![A_206]: (r1_tarski(k2_xboole_0(A_206, '#skF_3'), k2_xboole_0(A_206, '#skF_2')))), inference(resolution, [status(thm)], [c_7745, c_119])).
% 8.61/3.21  tff(c_8605, plain, (r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_8433])).
% 8.61/3.21  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.61/3.21  tff(c_13535, plain, (![A_271]: (r1_tarski(A_271, '#skF_2') | ~r1_tarski(A_271, k2_xboole_0('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_8605, c_8])).
% 8.61/3.21  tff(c_13591, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_232, c_13535])).
% 8.61/3.21  tff(c_13624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_13591])).
% 8.61/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.61/3.21  
% 8.61/3.21  Inference rules
% 8.61/3.21  ----------------------
% 8.61/3.21  #Ref     : 0
% 8.61/3.21  #Sup     : 3514
% 8.61/3.21  #Fact    : 0
% 8.61/3.21  #Define  : 0
% 8.61/3.21  #Split   : 0
% 8.61/3.21  #Chain   : 0
% 8.61/3.21  #Close   : 0
% 8.61/3.21  
% 8.61/3.21  Ordering : KBO
% 8.61/3.21  
% 8.61/3.21  Simplification rules
% 8.61/3.21  ----------------------
% 8.61/3.21  #Subsume      : 197
% 8.61/3.21  #Demod        : 1981
% 8.61/3.21  #Tautology    : 1881
% 8.61/3.21  #SimpNegUnit  : 1
% 8.61/3.21  #BackRed      : 0
% 8.61/3.21  
% 8.61/3.21  #Partial instantiations: 0
% 8.61/3.21  #Strategies tried      : 1
% 8.61/3.21  
% 8.61/3.21  Timing (in seconds)
% 8.61/3.21  ----------------------
% 8.61/3.21  Preprocessing        : 0.27
% 8.61/3.21  Parsing              : 0.15
% 8.61/3.21  CNF conversion       : 0.02
% 8.61/3.21  Main loop            : 2.18
% 8.61/3.21  Inferencing          : 0.52
% 8.61/3.21  Reduction            : 0.98
% 8.61/3.21  Demodulation         : 0.82
% 8.61/3.21  BG Simplification    : 0.06
% 8.61/3.21  Subsumption          : 0.50
% 8.61/3.21  Abstraction          : 0.07
% 8.61/3.21  MUC search           : 0.00
% 8.61/3.21  Cooper               : 0.00
% 8.61/3.21  Total                : 2.48
% 8.61/3.21  Index Insertion      : 0.00
% 8.61/3.21  Index Deletion       : 0.00
% 8.61/3.21  Index Matching       : 0.00
% 8.61/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
