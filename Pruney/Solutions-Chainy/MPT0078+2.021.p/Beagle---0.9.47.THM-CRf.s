%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  94 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 106 expanded)
%              Number of equality atoms :   37 (  77 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_26,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_291,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_299,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_291])).

tff(c_318,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_327,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_318])).

tff(c_59,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_10])).

tff(c_355,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_75])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_161])).

tff(c_179,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_782,plain,(
    ! [A_63,C_64,B_65] : k2_xboole_0(k4_xboole_0(A_63,C_64),k4_xboole_0(B_65,C_64)) = k4_xboole_0(k2_xboole_0(A_63,B_65),C_64) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_853,plain,(
    ! [A_14,B_65] : k4_xboole_0(k2_xboole_0(A_14,B_65),A_14) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_65,A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_782])).

tff(c_889,plain,(
    ! [A_14,B_65] : k4_xboole_0(k2_xboole_0(A_14,B_65),A_14) = k4_xboole_0(B_65,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_853])).

tff(c_28,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_298,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_291])).

tff(c_330,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_318])).

tff(c_384,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_32])).

tff(c_1471,plain,(
    ! [A_80,B_81] : k4_xboole_0(k2_xboole_0(A_80,B_81),A_80) = k4_xboole_0(B_81,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_853])).

tff(c_1526,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_1471])).

tff(c_1556,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_889,c_384,c_1526])).

tff(c_1558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.90  
% 3.55/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.90  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.91/1.90  
% 3.91/1.90  %Foreground sorts:
% 3.91/1.90  
% 3.91/1.90  
% 3.91/1.90  %Background operators:
% 3.91/1.90  
% 3.91/1.90  
% 3.91/1.90  %Foreground operators:
% 3.91/1.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.91/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.90  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.91/1.90  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.90  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.90  
% 3.91/1.92  tff(f_74, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.91/1.92  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.91/1.92  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.91/1.92  tff(f_65, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.91/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.91/1.92  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.91/1.92  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.91/1.92  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.91/1.92  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.91/1.92  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.91/1.92  tff(c_26, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.92  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.92  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.91/1.92  tff(c_151, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.92  tff(c_291, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_151])).
% 3.91/1.92  tff(c_299, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_291])).
% 3.91/1.92  tff(c_318, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.91/1.92  tff(c_327, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_299, c_318])).
% 3.91/1.92  tff(c_59, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.92  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.92  tff(c_75, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_59, c_10])).
% 3.91/1.92  tff(c_355, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_327, c_75])).
% 3.91/1.92  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.91/1.92  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.91/1.92  tff(c_161, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.92  tff(c_176, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_161])).
% 3.91/1.92  tff(c_179, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_176])).
% 3.91/1.92  tff(c_782, plain, (![A_63, C_64, B_65]: (k2_xboole_0(k4_xboole_0(A_63, C_64), k4_xboole_0(B_65, C_64))=k4_xboole_0(k2_xboole_0(A_63, B_65), C_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.92  tff(c_853, plain, (![A_14, B_65]: (k4_xboole_0(k2_xboole_0(A_14, B_65), A_14)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_65, A_14)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_782])).
% 3.91/1.92  tff(c_889, plain, (![A_14, B_65]: (k4_xboole_0(k2_xboole_0(A_14, B_65), A_14)=k4_xboole_0(B_65, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_853])).
% 3.91/1.92  tff(c_28, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.92  tff(c_298, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_291])).
% 3.91/1.92  tff(c_330, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_298, c_318])).
% 3.91/1.92  tff(c_384, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_330, c_75])).
% 3.91/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.92  tff(c_32, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.92  tff(c_33, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_32])).
% 3.91/1.92  tff(c_1471, plain, (![A_80, B_81]: (k4_xboole_0(k2_xboole_0(A_80, B_81), A_80)=k4_xboole_0(B_81, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_853])).
% 3.91/1.92  tff(c_1526, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_33, c_1471])).
% 3.91/1.92  tff(c_1556, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_355, c_889, c_384, c_1526])).
% 3.91/1.92  tff(c_1558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1556])).
% 3.91/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.92  
% 3.91/1.92  Inference rules
% 3.91/1.92  ----------------------
% 3.91/1.92  #Ref     : 0
% 3.91/1.92  #Sup     : 385
% 3.91/1.92  #Fact    : 0
% 3.91/1.92  #Define  : 0
% 3.91/1.92  #Split   : 1
% 3.91/1.92  #Chain   : 0
% 3.91/1.92  #Close   : 0
% 3.91/1.92  
% 3.91/1.92  Ordering : KBO
% 3.91/1.92  
% 3.91/1.92  Simplification rules
% 3.91/1.92  ----------------------
% 3.91/1.92  #Subsume      : 5
% 3.91/1.92  #Demod        : 257
% 3.91/1.92  #Tautology    : 253
% 3.91/1.92  #SimpNegUnit  : 5
% 3.91/1.92  #BackRed      : 2
% 3.91/1.92  
% 3.91/1.92  #Partial instantiations: 0
% 3.91/1.92  #Strategies tried      : 1
% 3.91/1.92  
% 3.91/1.92  Timing (in seconds)
% 3.91/1.92  ----------------------
% 3.91/1.92  Preprocessing        : 0.46
% 3.91/1.92  Parsing              : 0.25
% 3.91/1.92  CNF conversion       : 0.03
% 3.91/1.92  Main loop            : 0.66
% 3.91/1.92  Inferencing          : 0.22
% 3.91/1.92  Reduction            : 0.27
% 3.91/1.92  Demodulation         : 0.22
% 3.91/1.92  BG Simplification    : 0.03
% 3.91/1.92  Subsumption          : 0.09
% 3.91/1.92  Abstraction          : 0.03
% 3.91/1.92  MUC search           : 0.00
% 3.91/1.92  Cooper               : 0.00
% 3.91/1.92  Total                : 1.17
% 3.91/1.92  Index Insertion      : 0.00
% 3.91/1.92  Index Deletion       : 0.00
% 3.91/1.92  Index Matching       : 0.00
% 3.91/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
