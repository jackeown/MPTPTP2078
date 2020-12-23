%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 10.47s
% Output     : CNFRefutation 10.58s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  89 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_375,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_387,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_375])).

tff(c_763,plain,(
    ! [A_59,B_60] : k2_xboole_0(k3_xboole_0(A_59,B_60),k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_811,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_763])).

tff(c_179,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_14])).

tff(c_1099,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_207])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1182,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k4_xboole_0(A_67,B_68),C_69) = k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8408,plain,(
    ! [C_171,A_172,B_173] : k2_xboole_0(C_171,k4_xboole_0(A_172,k2_xboole_0(B_173,C_171))) = k2_xboole_0(C_171,k4_xboole_0(A_172,B_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1182,c_18])).

tff(c_10194,plain,(
    ! [A_182] : k2_xboole_0('#skF_3',k4_xboole_0(A_182,k2_xboole_0('#skF_4','#skF_5'))) = k2_xboole_0('#skF_3',k4_xboole_0(A_182,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8408])).

tff(c_10340,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10194])).

tff(c_10377,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1099,c_14,c_10340])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_386,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_375])).

tff(c_398,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_386])).

tff(c_808,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_763])).

tff(c_1418,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_207])).

tff(c_226,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_179])).

tff(c_290,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_24])).

tff(c_31348,plain,(
    ! [B_320,A_321,A_322] : k2_xboole_0(B_320,k4_xboole_0(A_321,k2_xboole_0(B_320,A_322))) = k2_xboole_0(B_320,k4_xboole_0(A_321,A_322)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8408])).

tff(c_31820,plain,(
    k2_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_31348])).

tff(c_31985,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10377,c_1418,c_14,c_31820])).

tff(c_31987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_31985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:39:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.47/4.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.71  
% 10.47/4.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.71  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.47/4.71  
% 10.47/4.71  %Foreground sorts:
% 10.47/4.71  
% 10.47/4.71  
% 10.47/4.71  %Background operators:
% 10.47/4.71  
% 10.47/4.71  
% 10.47/4.71  %Foreground operators:
% 10.47/4.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.47/4.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.47/4.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.47/4.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.47/4.71  tff('#skF_5', type, '#skF_5': $i).
% 10.47/4.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.47/4.71  tff('#skF_2', type, '#skF_2': $i).
% 10.47/4.71  tff('#skF_3', type, '#skF_3': $i).
% 10.47/4.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.47/4.71  tff('#skF_4', type, '#skF_4': $i).
% 10.47/4.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.47/4.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.47/4.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.47/4.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.47/4.71  
% 10.58/4.72  tff(f_72, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 10.58/4.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.58/4.72  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.58/4.72  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.58/4.72  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.58/4.72  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 10.58/4.72  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.58/4.72  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.58/4.72  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.58/4.72  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.58/4.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.58/4.72  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.58/4.72  tff(c_375, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.58/4.72  tff(c_387, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_375])).
% 10.58/4.72  tff(c_763, plain, (![A_59, B_60]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k4_xboole_0(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.58/4.72  tff(c_811, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_2'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_387, c_763])).
% 10.58/4.72  tff(c_179, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.58/4.72  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.58/4.72  tff(c_207, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_179, c_14])).
% 10.58/4.72  tff(c_1099, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_811, c_207])).
% 10.58/4.72  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.58/4.72  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.58/4.72  tff(c_1182, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k4_xboole_0(A_67, B_68), C_69)=k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.58/4.72  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.58/4.72  tff(c_8408, plain, (![C_171, A_172, B_173]: (k2_xboole_0(C_171, k4_xboole_0(A_172, k2_xboole_0(B_173, C_171)))=k2_xboole_0(C_171, k4_xboole_0(A_172, B_173)))), inference(superposition, [status(thm), theory('equality')], [c_1182, c_18])).
% 10.58/4.72  tff(c_10194, plain, (![A_182]: (k2_xboole_0('#skF_3', k4_xboole_0(A_182, k2_xboole_0('#skF_4', '#skF_5')))=k2_xboole_0('#skF_3', k4_xboole_0(A_182, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_8408])).
% 10.58/4.72  tff(c_10340, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_10194])).
% 10.58/4.72  tff(c_10377, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1099, c_14, c_10340])).
% 10.58/4.72  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.58/4.72  tff(c_32, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.58/4.72  tff(c_386, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_375])).
% 10.58/4.72  tff(c_398, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_386])).
% 10.58/4.72  tff(c_808, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_398, c_763])).
% 10.58/4.72  tff(c_1418, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_808, c_207])).
% 10.58/4.72  tff(c_226, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_179])).
% 10.58/4.72  tff(c_290, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_226, c_24])).
% 10.58/4.72  tff(c_31348, plain, (![B_320, A_321, A_322]: (k2_xboole_0(B_320, k4_xboole_0(A_321, k2_xboole_0(B_320, A_322)))=k2_xboole_0(B_320, k4_xboole_0(A_321, A_322)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8408])).
% 10.58/4.72  tff(c_31820, plain, (k2_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_290, c_31348])).
% 10.58/4.72  tff(c_31985, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10377, c_1418, c_14, c_31820])).
% 10.58/4.72  tff(c_31987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_31985])).
% 10.58/4.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.58/4.72  
% 10.58/4.72  Inference rules
% 10.58/4.72  ----------------------
% 10.58/4.72  #Ref     : 0
% 10.58/4.72  #Sup     : 8161
% 10.58/4.72  #Fact    : 0
% 10.58/4.72  #Define  : 0
% 10.58/4.72  #Split   : 8
% 10.58/4.72  #Chain   : 0
% 10.58/4.72  #Close   : 0
% 10.58/4.72  
% 10.58/4.72  Ordering : KBO
% 10.58/4.72  
% 10.58/4.72  Simplification rules
% 10.58/4.72  ----------------------
% 10.58/4.72  #Subsume      : 201
% 10.58/4.72  #Demod        : 8820
% 10.58/4.72  #Tautology    : 5710
% 10.58/4.72  #SimpNegUnit  : 39
% 10.58/4.72  #BackRed      : 12
% 10.58/4.72  
% 10.58/4.72  #Partial instantiations: 0
% 10.58/4.72  #Strategies tried      : 1
% 10.58/4.72  
% 10.58/4.72  Timing (in seconds)
% 10.58/4.72  ----------------------
% 10.58/4.73  Preprocessing        : 0.28
% 10.58/4.73  Parsing              : 0.15
% 10.58/4.73  CNF conversion       : 0.02
% 10.58/4.73  Main loop            : 3.70
% 10.58/4.73  Inferencing          : 0.66
% 10.58/4.73  Reduction            : 2.16
% 10.58/4.73  Demodulation         : 1.91
% 10.58/4.73  BG Simplification    : 0.07
% 10.58/4.73  Subsumption          : 0.63
% 10.58/4.73  Abstraction          : 0.11
% 10.58/4.73  MUC search           : 0.00
% 10.58/4.73  Cooper               : 0.00
% 10.58/4.73  Total                : 4.01
% 10.58/4.73  Index Insertion      : 0.00
% 10.58/4.73  Index Deletion       : 0.00
% 10.58/4.73  Index Matching       : 0.00
% 10.58/4.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
