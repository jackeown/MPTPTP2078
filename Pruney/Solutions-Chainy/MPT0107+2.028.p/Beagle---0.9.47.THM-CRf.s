%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 128 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 175 expanded)
%              Number of equality atoms :   42 ( 110 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k3_xboole_0(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_28,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_911,plain,(
    ! [A_79] : k4_xboole_0(A_79,k3_xboole_0(A_79,k1_xboole_0)) = k3_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_28])).

tff(c_26,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_958,plain,(
    ! [A_79] : k4_xboole_0(A_79,k1_xboole_0) = k3_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_26])).

tff(c_1000,plain,(
    ! [A_79] : k3_xboole_0(A_79,A_79) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_958])).

tff(c_129,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_765,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),A_70)
      | r2_hidden('#skF_2'(A_70,B_71,C_72),C_72)
      | k4_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_768,plain,(
    ! [A_70,C_72] :
      ( r2_hidden('#skF_2'(A_70,A_70,C_72),C_72)
      | k4_xboole_0(A_70,A_70) = C_72 ) ),
    inference(resolution,[status(thm)],[c_765,c_18])).

tff(c_798,plain,(
    ! [A_70,C_72] :
      ( r2_hidden('#skF_2'(A_70,A_70,C_72),C_72)
      | k3_xboole_0(A_70,k1_xboole_0) = C_72 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_768])).

tff(c_2808,plain,(
    ! [A_134,C_135] :
      ( r2_hidden('#skF_2'(A_134,A_134,C_135),C_135)
      | k3_xboole_0(A_134,k1_xboole_0) = C_135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_768])).

tff(c_186,plain,(
    ! [D_34,B_35,A_36] :
      ( ~ r2_hidden(D_34,B_35)
      | ~ r2_hidden(D_34,k4_xboole_0(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [D_34,A_11] :
      ( ~ r2_hidden(D_34,k1_xboole_0)
      | ~ r2_hidden(D_34,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_186])).

tff(c_2853,plain,(
    ! [A_136,A_137] :
      ( ~ r2_hidden('#skF_2'(A_136,A_136,k1_xboole_0),A_137)
      | k3_xboole_0(A_136,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2808,c_198])).

tff(c_2870,plain,(
    ! [A_70] : k3_xboole_0(A_70,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_798,c_2853])).

tff(c_3173,plain,(
    ! [A_141] : k4_xboole_0(A_141,A_141) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2870,c_129])).

tff(c_32,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3223,plain,(
    ! [A_141] : k2_xboole_0(k3_xboole_0(A_141,A_141),k1_xboole_0) = A_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_3173,c_32])).

tff(c_3268,plain,(
    ! [A_141] : k2_xboole_0(A_141,k1_xboole_0) = A_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_3223])).

tff(c_160,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3249,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(B_17,k3_xboole_0(A_16,B_17))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3173])).

tff(c_3273,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_3249])).

tff(c_376,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),k4_xboole_0(B_50,A_49)) = k5_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_391,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),k4_xboole_0(k3_xboole_0(A_12,B_13),A_12)) = k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_376])).

tff(c_415,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,k4_xboole_0(B_13,A_12))) = k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_391])).

tff(c_4577,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k3_xboole_0(A_179,B_180)) = k4_xboole_0(A_179,B_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3268,c_3273,c_415])).

tff(c_4626,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4577])).

tff(c_36,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_5363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.91  
% 4.71/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.91  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.71/1.91  
% 4.71/1.91  %Foreground sorts:
% 4.71/1.91  
% 4.71/1.91  
% 4.71/1.91  %Background operators:
% 4.71/1.91  
% 4.71/1.91  
% 4.71/1.91  %Foreground operators:
% 4.71/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/1.91  
% 4.71/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.71/1.93  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.71/1.93  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.71/1.93  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.71/1.93  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.71/1.93  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.71/1.93  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.71/1.93  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.71/1.93  tff(f_54, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.71/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.71/1.93  tff(c_24, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.71/1.93  tff(c_111, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.71/1.93  tff(c_132, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k3_xboole_0(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_111])).
% 4.71/1.93  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.71/1.93  tff(c_911, plain, (![A_79]: (k4_xboole_0(A_79, k3_xboole_0(A_79, k1_xboole_0))=k3_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_132, c_28])).
% 4.71/1.93  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/1.93  tff(c_958, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=k3_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_911, c_26])).
% 4.71/1.93  tff(c_1000, plain, (![A_79]: (k3_xboole_0(A_79, A_79)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_958])).
% 4.71/1.93  tff(c_129, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_111])).
% 4.71/1.93  tff(c_765, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), A_70) | r2_hidden('#skF_2'(A_70, B_71, C_72), C_72) | k4_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/1.93  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/1.93  tff(c_768, plain, (![A_70, C_72]: (r2_hidden('#skF_2'(A_70, A_70, C_72), C_72) | k4_xboole_0(A_70, A_70)=C_72)), inference(resolution, [status(thm)], [c_765, c_18])).
% 4.71/1.93  tff(c_798, plain, (![A_70, C_72]: (r2_hidden('#skF_2'(A_70, A_70, C_72), C_72) | k3_xboole_0(A_70, k1_xboole_0)=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_768])).
% 4.71/1.93  tff(c_2808, plain, (![A_134, C_135]: (r2_hidden('#skF_2'(A_134, A_134, C_135), C_135) | k3_xboole_0(A_134, k1_xboole_0)=C_135)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_768])).
% 4.71/1.93  tff(c_186, plain, (![D_34, B_35, A_36]: (~r2_hidden(D_34, B_35) | ~r2_hidden(D_34, k4_xboole_0(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/1.93  tff(c_198, plain, (![D_34, A_11]: (~r2_hidden(D_34, k1_xboole_0) | ~r2_hidden(D_34, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_186])).
% 4.71/1.93  tff(c_2853, plain, (![A_136, A_137]: (~r2_hidden('#skF_2'(A_136, A_136, k1_xboole_0), A_137) | k3_xboole_0(A_136, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2808, c_198])).
% 4.71/1.93  tff(c_2870, plain, (![A_70]: (k3_xboole_0(A_70, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_798, c_2853])).
% 4.71/1.93  tff(c_3173, plain, (![A_141]: (k4_xboole_0(A_141, A_141)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2870, c_129])).
% 4.71/1.93  tff(c_32, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/1.93  tff(c_3223, plain, (![A_141]: (k2_xboole_0(k3_xboole_0(A_141, A_141), k1_xboole_0)=A_141)), inference(superposition, [status(thm), theory('equality')], [c_3173, c_32])).
% 4.71/1.93  tff(c_3268, plain, (![A_141]: (k2_xboole_0(A_141, k1_xboole_0)=A_141)), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_3223])).
% 4.71/1.93  tff(c_160, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/1.93  tff(c_178, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_160])).
% 4.71/1.93  tff(c_30, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.93  tff(c_3249, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(B_17, k3_xboole_0(A_16, B_17)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_3173])).
% 4.71/1.93  tff(c_3273, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_3249])).
% 4.71/1.93  tff(c_376, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k4_xboole_0(B_50, A_49))=k5_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/1.93  tff(c_391, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k4_xboole_0(k3_xboole_0(A_12, B_13), A_12))=k5_xboole_0(A_12, k3_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_376])).
% 4.71/1.93  tff(c_415, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, k4_xboole_0(B_13, A_12)))=k5_xboole_0(A_12, k3_xboole_0(A_12, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_391])).
% 4.71/1.93  tff(c_4577, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k3_xboole_0(A_179, B_180))=k4_xboole_0(A_179, B_180))), inference(demodulation, [status(thm), theory('equality')], [c_3268, c_3273, c_415])).
% 4.71/1.93  tff(c_4626, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4577])).
% 4.71/1.93  tff(c_36, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.93  tff(c_37, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 4.71/1.93  tff(c_5363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4626, c_37])).
% 4.71/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.93  
% 4.71/1.93  Inference rules
% 4.71/1.93  ----------------------
% 4.71/1.93  #Ref     : 0
% 4.71/1.93  #Sup     : 1256
% 4.71/1.93  #Fact    : 0
% 4.71/1.93  #Define  : 0
% 4.71/1.93  #Split   : 0
% 4.71/1.93  #Chain   : 0
% 4.71/1.93  #Close   : 0
% 4.71/1.93  
% 4.71/1.93  Ordering : KBO
% 4.71/1.93  
% 4.71/1.93  Simplification rules
% 4.71/1.93  ----------------------
% 4.71/1.93  #Subsume      : 81
% 4.71/1.93  #Demod        : 1137
% 4.71/1.93  #Tautology    : 786
% 4.71/1.93  #SimpNegUnit  : 0
% 4.71/1.93  #BackRed      : 29
% 4.71/1.93  
% 4.71/1.93  #Partial instantiations: 0
% 4.71/1.93  #Strategies tried      : 1
% 4.71/1.93  
% 4.71/1.93  Timing (in seconds)
% 4.71/1.93  ----------------------
% 4.71/1.93  Preprocessing        : 0.31
% 4.71/1.93  Parsing              : 0.15
% 4.71/1.93  CNF conversion       : 0.02
% 4.71/1.93  Main loop            : 0.85
% 4.71/1.93  Inferencing          : 0.27
% 4.71/1.93  Reduction            : 0.37
% 4.71/1.93  Demodulation         : 0.30
% 4.71/1.93  BG Simplification    : 0.04
% 4.71/1.93  Subsumption          : 0.12
% 4.71/1.93  Abstraction          : 0.05
% 4.71/1.93  MUC search           : 0.00
% 4.71/1.93  Cooper               : 0.00
% 4.71/1.93  Total                : 1.19
% 4.71/1.93  Index Insertion      : 0.00
% 4.71/1.93  Index Deletion       : 0.00
% 4.71/1.93  Index Matching       : 0.00
% 4.71/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
