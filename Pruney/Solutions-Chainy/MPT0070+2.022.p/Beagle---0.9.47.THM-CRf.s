%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 103 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 ( 124 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_131,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | k3_xboole_0(A_35,B_34) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_24])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_141,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_141])).

tff(c_202,plain,(
    ! [A_36,B_37] : k2_xboole_0(k3_xboole_0(A_36,B_37),k4_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_211,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_202])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_14] : k2_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_263,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_76])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_285,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_20])).

tff(c_291,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_285])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_158,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_176,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_495,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_981,plain,(
    ! [C_55] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_55)) = k4_xboole_0('#skF_4',C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_495])).

tff(c_1002,plain,(
    k4_xboole_0('#skF_4','#skF_2') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_981])).

tff(c_1019,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1002])).

tff(c_1030,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_20])).

tff(c_1037,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_1030])).

tff(c_1039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:54:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.38  
% 2.85/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.85/1.38  
% 2.85/1.38  %Foreground sorts:
% 2.85/1.38  
% 2.85/1.38  
% 2.85/1.38  %Background operators:
% 2.85/1.38  
% 2.85/1.38  
% 2.85/1.38  %Foreground operators:
% 2.85/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.38  
% 2.85/1.40  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.85/1.40  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.85/1.40  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.85/1.40  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.85/1.40  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.85/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.85/1.40  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.85/1.40  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.85/1.40  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.85/1.40  tff(c_131, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.40  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_190, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | k3_xboole_0(A_35, B_34)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_131, c_8])).
% 2.85/1.40  tff(c_24, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.40  tff(c_201, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_24])).
% 2.85/1.40  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.40  tff(c_85, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_88, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.85/1.40  tff(c_141, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.40  tff(c_152, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_141])).
% 2.85/1.40  tff(c_202, plain, (![A_36, B_37]: (k2_xboole_0(k3_xboole_0(A_36, B_37), k4_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.85/1.40  tff(c_211, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_152, c_202])).
% 2.85/1.40  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.85/1.40  tff(c_38, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.40  tff(c_76, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14)), inference(superposition, [status(thm), theory('equality')], [c_16, c_38])).
% 2.85/1.40  tff(c_263, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_211, c_76])).
% 2.85/1.40  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.40  tff(c_285, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_263, c_20])).
% 2.85/1.40  tff(c_291, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_152, c_285])).
% 2.85/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.40  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.40  tff(c_158, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.85/1.40  tff(c_162, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_158])).
% 2.85/1.40  tff(c_176, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_162])).
% 2.85/1.40  tff(c_495, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.40  tff(c_981, plain, (![C_55]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_55))=k4_xboole_0('#skF_4', C_55))), inference(superposition, [status(thm), theory('equality')], [c_263, c_495])).
% 2.85/1.40  tff(c_1002, plain, (k4_xboole_0('#skF_4', '#skF_2')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_176, c_981])).
% 2.85/1.40  tff(c_1019, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1002])).
% 2.85/1.40  tff(c_1030, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_20])).
% 2.85/1.40  tff(c_1037, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_291, c_1030])).
% 2.85/1.40  tff(c_1039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_1037])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  Inference rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Ref     : 0
% 2.85/1.40  #Sup     : 281
% 2.85/1.40  #Fact    : 0
% 2.85/1.40  #Define  : 0
% 2.85/1.40  #Split   : 2
% 2.85/1.40  #Chain   : 0
% 2.85/1.40  #Close   : 0
% 2.85/1.40  
% 2.85/1.40  Ordering : KBO
% 2.85/1.40  
% 2.85/1.40  Simplification rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Subsume      : 9
% 2.85/1.40  #Demod        : 218
% 2.85/1.40  #Tautology    : 177
% 2.85/1.40  #SimpNegUnit  : 8
% 2.85/1.40  #BackRed      : 8
% 2.85/1.40  
% 2.85/1.40  #Partial instantiations: 0
% 2.85/1.40  #Strategies tried      : 1
% 2.85/1.40  
% 2.85/1.40  Timing (in seconds)
% 2.85/1.40  ----------------------
% 2.85/1.40  Preprocessing        : 0.27
% 2.85/1.40  Parsing              : 0.15
% 2.85/1.40  CNF conversion       : 0.02
% 2.85/1.40  Main loop            : 0.37
% 2.85/1.40  Inferencing          : 0.13
% 2.85/1.40  Reduction            : 0.15
% 2.85/1.40  Demodulation         : 0.12
% 2.85/1.40  BG Simplification    : 0.02
% 2.85/1.40  Subsumption          : 0.05
% 2.85/1.40  Abstraction          : 0.02
% 2.85/1.40  MUC search           : 0.00
% 2.85/1.40  Cooper               : 0.00
% 2.85/1.40  Total                : 0.67
% 2.85/1.40  Index Insertion      : 0.00
% 2.85/1.40  Index Deletion       : 0.00
% 2.85/1.40  Index Matching       : 0.00
% 2.85/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
