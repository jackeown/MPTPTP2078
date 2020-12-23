%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 136 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 160 expanded)
%              Number of equality atoms :   44 ( 117 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_207,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_200])).

tff(c_28,plain,(
    ! [A_24,B_25] : k2_xboole_0(k3_xboole_0(A_24,B_25),k4_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_212,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_28])).

tff(c_68,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_236,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_36])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_454,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_306,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_333,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_306])).

tff(c_339,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_333])).

tff(c_464,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k2_xboole_0(B_58,k4_xboole_0(A_57,B_58))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_339])).

tff(c_526,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,A_60)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_464])).

tff(c_571,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_526])).

tff(c_2913,plain,(
    ! [C_109,A_110,B_111] : k2_xboole_0(C_109,k4_xboole_0(A_110,k2_xboole_0(B_111,C_109))) = k2_xboole_0(C_109,k4_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_20])).

tff(c_3029,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_2913])).

tff(c_3104,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_16,c_3029])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_208,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_200])).

tff(c_224,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_28])).

tff(c_284,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_84])).

tff(c_556,plain,(
    ! [B_17,A_16] : k4_xboole_0(k4_xboole_0(B_17,A_16),k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_526])).

tff(c_3661,plain,(
    ! [A_115] : k2_xboole_0('#skF_5',k4_xboole_0(A_115,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_5',k4_xboole_0(A_115,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_2913])).

tff(c_3716,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_3661])).

tff(c_3764,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_2,c_284,c_284,c_16,c_3716])).

tff(c_3766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.81  
% 4.22/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.22/1.81  
% 4.22/1.81  %Foreground sorts:
% 4.22/1.81  
% 4.22/1.81  
% 4.22/1.81  %Background operators:
% 4.22/1.81  
% 4.22/1.81  
% 4.22/1.81  %Foreground operators:
% 4.22/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.22/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.22/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.22/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.22/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.22/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.22/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.22/1.81  
% 4.39/1.83  tff(f_80, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 4.39/1.83  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.39/1.83  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.39/1.83  tff(f_71, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.39/1.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.39/1.83  tff(f_59, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.39/1.83  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.39/1.83  tff(f_67, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.39/1.83  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.39/1.83  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.39/1.83  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.39/1.83  tff(c_30, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.39/1.83  tff(c_32, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.39/1.83  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.39/1.83  tff(c_166, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.39/1.83  tff(c_200, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_166])).
% 4.39/1.83  tff(c_207, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_200])).
% 4.39/1.83  tff(c_28, plain, (![A_24, B_25]: (k2_xboole_0(k3_xboole_0(A_24, B_25), k4_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.39/1.83  tff(c_212, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_207, c_28])).
% 4.39/1.83  tff(c_68, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.83  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.39/1.83  tff(c_84, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_68, c_16])).
% 4.39/1.83  tff(c_236, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_212, c_84])).
% 4.39/1.83  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.83  tff(c_36, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.39/1.83  tff(c_37, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_36])).
% 4.39/1.83  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.39/1.83  tff(c_454, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.83  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.39/1.83  tff(c_22, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.39/1.83  tff(c_306, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.39/1.83  tff(c_333, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_306])).
% 4.39/1.83  tff(c_339, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_333])).
% 4.39/1.83  tff(c_464, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k2_xboole_0(B_58, k4_xboole_0(A_57, B_58)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_454, c_339])).
% 4.39/1.83  tff(c_526, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, A_60))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_464])).
% 4.39/1.83  tff(c_571, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_526])).
% 4.39/1.83  tff(c_2913, plain, (![C_109, A_110, B_111]: (k2_xboole_0(C_109, k4_xboole_0(A_110, k2_xboole_0(B_111, C_109)))=k2_xboole_0(C_109, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_454, c_20])).
% 4.39/1.83  tff(c_3029, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_571, c_2913])).
% 4.39/1.83  tff(c_3104, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_16, c_3029])).
% 4.39/1.83  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.39/1.83  tff(c_208, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_200])).
% 4.39/1.83  tff(c_224, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_208, c_28])).
% 4.39/1.83  tff(c_284, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_224, c_84])).
% 4.39/1.83  tff(c_556, plain, (![B_17, A_16]: (k4_xboole_0(k4_xboole_0(B_17, A_16), k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_526])).
% 4.39/1.83  tff(c_3661, plain, (![A_115]: (k2_xboole_0('#skF_5', k4_xboole_0(A_115, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_5', k4_xboole_0(A_115, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_37, c_2913])).
% 4.39/1.83  tff(c_3716, plain, (k2_xboole_0('#skF_5', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_556, c_3661])).
% 4.39/1.83  tff(c_3764, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_2, c_284, c_284, c_16, c_3716])).
% 4.39/1.83  tff(c_3766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3764])).
% 4.39/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.83  
% 4.39/1.83  Inference rules
% 4.39/1.83  ----------------------
% 4.39/1.83  #Ref     : 0
% 4.39/1.83  #Sup     : 941
% 4.39/1.83  #Fact    : 0
% 4.39/1.83  #Define  : 0
% 4.39/1.83  #Split   : 4
% 4.39/1.83  #Chain   : 0
% 4.39/1.83  #Close   : 0
% 4.39/1.83  
% 4.39/1.83  Ordering : KBO
% 4.39/1.83  
% 4.39/1.83  Simplification rules
% 4.39/1.83  ----------------------
% 4.39/1.83  #Subsume      : 5
% 4.39/1.83  #Demod        : 927
% 4.39/1.83  #Tautology    : 650
% 4.39/1.83  #SimpNegUnit  : 5
% 4.39/1.83  #BackRed      : 2
% 4.39/1.83  
% 4.39/1.83  #Partial instantiations: 0
% 4.39/1.83  #Strategies tried      : 1
% 4.39/1.83  
% 4.39/1.83  Timing (in seconds)
% 4.39/1.83  ----------------------
% 4.39/1.83  Preprocessing        : 0.30
% 4.39/1.83  Parsing              : 0.17
% 4.39/1.83  CNF conversion       : 0.02
% 4.39/1.83  Main loop            : 0.70
% 4.39/1.83  Inferencing          : 0.21
% 4.39/1.83  Reduction            : 0.33
% 4.39/1.83  Demodulation         : 0.28
% 4.39/1.83  BG Simplification    : 0.03
% 4.39/1.83  Subsumption          : 0.09
% 4.39/1.83  Abstraction          : 0.03
% 4.39/1.83  MUC search           : 0.00
% 4.39/1.83  Cooper               : 0.00
% 4.39/1.83  Total                : 1.03
% 4.39/1.83  Index Insertion      : 0.00
% 4.39/1.83  Index Deletion       : 0.00
% 4.39/1.83  Index Matching       : 0.00
% 4.39/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
