%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 112 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 121 expanded)
%              Number of equality atoms :   41 (  99 expanded)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_157,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_157])).

tff(c_202,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,B_39),k4_xboole_0(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_220,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_202])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_241,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_7,k1_xboole_0)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_202])).

tff(c_247,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_241])).

tff(c_1362,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_249,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_241])).

tff(c_275,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_79,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(B_31,A_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_141,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_122])).

tff(c_1052,plain,(
    ! [A_63,B_64,C_65] : k4_xboole_0(k4_xboole_0(A_63,B_64),C_65) = k4_xboole_0(A_63,k2_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5774,plain,(
    ! [C_124,A_125,B_126] : k2_xboole_0(C_124,k4_xboole_0(A_125,k2_xboole_0(B_126,C_124))) = k2_xboole_0(C_124,k4_xboole_0(A_125,B_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_14])).

tff(c_6007,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_5774])).

tff(c_6087,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_275,c_6007])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_177,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_223,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_202])).

tff(c_629,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_247])).

tff(c_94,plain,(
    ! [A_29,B_28] : k4_xboole_0(A_29,k2_xboole_0(B_28,A_29)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_9111,plain,(
    ! [A_147] : k2_xboole_0('#skF_2',k4_xboole_0(A_147,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_147,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_5774])).

tff(c_9236,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_9111])).

tff(c_9276,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6087,c_2,c_629,c_275,c_9236])).

tff(c_9278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_9276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.36  
% 6.16/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.36  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.16/2.36  
% 6.16/2.36  %Foreground sorts:
% 6.16/2.36  
% 6.16/2.36  
% 6.16/2.36  %Background operators:
% 6.16/2.36  
% 6.16/2.36  
% 6.16/2.36  %Foreground operators:
% 6.16/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.16/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.16/2.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.16/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.16/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.16/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.16/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.16/2.36  
% 6.16/2.38  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.16/2.38  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.16/2.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.16/2.38  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.16/2.38  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.16/2.38  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.16/2.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.16/2.38  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.16/2.38  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.16/2.38  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.16/2.38  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.38  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.38  tff(c_64, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.16/2.38  tff(c_69, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_64])).
% 6.16/2.38  tff(c_157, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.16/2.38  tff(c_175, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_157])).
% 6.16/2.38  tff(c_202, plain, (![A_38, B_39]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k4_xboole_0(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.16/2.38  tff(c_220, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_175, c_202])).
% 6.16/2.38  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.38  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.16/2.38  tff(c_241, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_7, k1_xboole_0))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_10, c_202])).
% 6.16/2.38  tff(c_247, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_241])).
% 6.16/2.38  tff(c_1362, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_220, c_247])).
% 6.16/2.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.16/2.38  tff(c_249, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_241])).
% 6.16/2.38  tff(c_275, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 6.16/2.38  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.38  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 6.16/2.38  tff(c_79, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.16/2.38  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.16/2.38  tff(c_122, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(B_31, A_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 6.16/2.38  tff(c_141, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33, c_122])).
% 6.16/2.38  tff(c_1052, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k4_xboole_0(A_63, B_64), C_65)=k4_xboole_0(A_63, k2_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.16/2.38  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.16/2.38  tff(c_5774, plain, (![C_124, A_125, B_126]: (k2_xboole_0(C_124, k4_xboole_0(A_125, k2_xboole_0(B_126, C_124)))=k2_xboole_0(C_124, k4_xboole_0(A_125, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_1052, c_14])).
% 6.16/2.38  tff(c_6007, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_5774])).
% 6.16/2.38  tff(c_6087, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_275, c_6007])).
% 6.16/2.38  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.38  tff(c_177, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_157])).
% 6.16/2.38  tff(c_223, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_177, c_202])).
% 6.16/2.38  tff(c_629, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_223, c_247])).
% 6.16/2.38  tff(c_94, plain, (![A_29, B_28]: (k4_xboole_0(A_29, k2_xboole_0(B_28, A_29))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 6.16/2.38  tff(c_9111, plain, (![A_147]: (k2_xboole_0('#skF_2', k4_xboole_0(A_147, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_147, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_33, c_5774])).
% 6.16/2.38  tff(c_9236, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_9111])).
% 6.16/2.38  tff(c_9276, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6087, c_2, c_629, c_275, c_9236])).
% 6.16/2.38  tff(c_9278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_9276])).
% 6.16/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.38  
% 6.16/2.38  Inference rules
% 6.16/2.38  ----------------------
% 6.16/2.38  #Ref     : 1
% 6.16/2.38  #Sup     : 2346
% 6.16/2.38  #Fact    : 0
% 6.16/2.38  #Define  : 0
% 6.16/2.38  #Split   : 0
% 6.16/2.38  #Chain   : 0
% 6.16/2.38  #Close   : 0
% 6.16/2.38  
% 6.16/2.38  Ordering : KBO
% 6.16/2.38  
% 6.16/2.38  Simplification rules
% 6.16/2.38  ----------------------
% 6.16/2.38  #Subsume      : 13
% 6.16/2.38  #Demod        : 2431
% 6.16/2.38  #Tautology    : 1688
% 6.16/2.38  #SimpNegUnit  : 3
% 6.16/2.38  #BackRed      : 5
% 6.16/2.38  
% 6.16/2.38  #Partial instantiations: 0
% 6.16/2.38  #Strategies tried      : 1
% 6.16/2.38  
% 6.16/2.38  Timing (in seconds)
% 6.16/2.38  ----------------------
% 6.16/2.38  Preprocessing        : 0.31
% 6.16/2.38  Parsing              : 0.17
% 6.16/2.38  CNF conversion       : 0.02
% 6.16/2.38  Main loop            : 1.28
% 6.16/2.38  Inferencing          : 0.36
% 6.16/2.38  Reduction            : 0.64
% 6.16/2.38  Demodulation         : 0.54
% 6.16/2.38  BG Simplification    : 0.04
% 6.16/2.38  Subsumption          : 0.17
% 6.16/2.38  Abstraction          : 0.06
% 6.16/2.38  MUC search           : 0.00
% 6.16/2.38  Cooper               : 0.00
% 6.16/2.38  Total                : 1.61
% 6.16/2.38  Index Insertion      : 0.00
% 6.16/2.38  Index Deletion       : 0.00
% 6.16/2.38  Index Matching       : 0.00
% 6.16/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
