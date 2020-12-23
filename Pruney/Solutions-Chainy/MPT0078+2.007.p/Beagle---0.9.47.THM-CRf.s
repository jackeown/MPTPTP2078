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
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   47 (  74 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  79 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_24,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_231,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_243,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_252,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_261,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_252])).

tff(c_143,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [A_26] : k2_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_10])).

tff(c_287,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_159])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_305,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_326,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_330,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_326])).

tff(c_695,plain,(
    ! [A_45,C_46,B_47] : k2_xboole_0(k4_xboole_0(A_45,C_46),k4_xboole_0(B_47,C_46)) = k4_xboole_0(k2_xboole_0(A_45,B_47),C_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_745,plain,(
    ! [A_45,A_11] : k4_xboole_0(k2_xboole_0(A_45,A_11),A_11) = k2_xboole_0(k4_xboole_0(A_45,A_11),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_695])).

tff(c_780,plain,(
    ! [A_45,A_11] : k4_xboole_0(k2_xboole_0(A_45,A_11),A_11) = k4_xboole_0(A_45,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_745])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_242,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_264,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_252])).

tff(c_392,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_159])).

tff(c_30,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_785,plain,(
    ! [A_48,A_49] : k4_xboole_0(k2_xboole_0(A_48,A_49),A_49) = k4_xboole_0(A_48,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_745])).

tff(c_840,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_785])).

tff(c_860,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_780,c_392,c_840])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.34  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.34  
% 2.30/1.34  %Foreground sorts:
% 2.30/1.34  
% 2.30/1.34  
% 2.30/1.34  %Background operators:
% 2.30/1.34  
% 2.30/1.34  
% 2.30/1.34  %Foreground operators:
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.34  
% 2.60/1.35  tff(f_56, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.60/1.35  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.60/1.35  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.60/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.60/1.35  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.60/1.35  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.35  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.35  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.60/1.35  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.60/1.35  tff(c_24, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.35  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.35  tff(c_231, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.35  tff(c_243, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_231])).
% 2.60/1.35  tff(c_252, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.35  tff(c_261, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_243, c_252])).
% 2.60/1.35  tff(c_143, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.35  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.35  tff(c_159, plain, (![A_26]: (k2_xboole_0(k1_xboole_0, A_26)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_143, c_10])).
% 2.60/1.35  tff(c_287, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_261, c_159])).
% 2.60/1.35  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.35  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.35  tff(c_305, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.35  tff(c_326, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_305])).
% 2.60/1.35  tff(c_330, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_326])).
% 2.60/1.35  tff(c_695, plain, (![A_45, C_46, B_47]: (k2_xboole_0(k4_xboole_0(A_45, C_46), k4_xboole_0(B_47, C_46))=k4_xboole_0(k2_xboole_0(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.35  tff(c_745, plain, (![A_45, A_11]: (k4_xboole_0(k2_xboole_0(A_45, A_11), A_11)=k2_xboole_0(k4_xboole_0(A_45, A_11), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_330, c_695])).
% 2.60/1.35  tff(c_780, plain, (![A_45, A_11]: (k4_xboole_0(k2_xboole_0(A_45, A_11), A_11)=k4_xboole_0(A_45, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_745])).
% 2.60/1.35  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.35  tff(c_242, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_231])).
% 2.60/1.35  tff(c_264, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_242, c_252])).
% 2.60/1.35  tff(c_392, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_264, c_159])).
% 2.60/1.35  tff(c_30, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.35  tff(c_785, plain, (![A_48, A_49]: (k4_xboole_0(k2_xboole_0(A_48, A_49), A_49)=k4_xboole_0(A_48, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_745])).
% 2.60/1.35  tff(c_840, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_785])).
% 2.60/1.35  tff(c_860, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_287, c_780, c_392, c_840])).
% 2.60/1.35  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_860])).
% 2.60/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.35  
% 2.60/1.35  Inference rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Ref     : 0
% 2.60/1.35  #Sup     : 213
% 2.60/1.35  #Fact    : 0
% 2.60/1.35  #Define  : 0
% 2.60/1.35  #Split   : 0
% 2.60/1.35  #Chain   : 0
% 2.60/1.35  #Close   : 0
% 2.60/1.35  
% 2.60/1.35  Ordering : KBO
% 2.60/1.35  
% 2.60/1.35  Simplification rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Subsume      : 0
% 2.60/1.35  #Demod        : 155
% 2.60/1.35  #Tautology    : 164
% 2.60/1.35  #SimpNegUnit  : 1
% 2.60/1.35  #BackRed      : 5
% 2.60/1.35  
% 2.60/1.35  #Partial instantiations: 0
% 2.60/1.35  #Strategies tried      : 1
% 2.60/1.35  
% 2.60/1.35  Timing (in seconds)
% 2.60/1.35  ----------------------
% 2.60/1.35  Preprocessing        : 0.28
% 2.60/1.35  Parsing              : 0.15
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.30
% 2.60/1.35  Inferencing          : 0.11
% 2.60/1.35  Reduction            : 0.12
% 2.60/1.35  Demodulation         : 0.10
% 2.60/1.35  BG Simplification    : 0.01
% 2.60/1.36  Subsumption          : 0.04
% 2.60/1.36  Abstraction          : 0.01
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.60/1.36  Total                : 0.61
% 2.60/1.36  Index Insertion      : 0.00
% 2.60/1.36  Index Deletion       : 0.00
% 2.60/1.36  Index Matching       : 0.00
% 2.60/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
