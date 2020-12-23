%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 111 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_999,plain,(
    ! [A_87,B_88] : r1_xboole_0(k4_xboole_0(A_87,B_88),k4_xboole_0(B_88,A_87)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1008,plain,(
    ! [B_88] : k4_xboole_0(B_88,B_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_999,c_20])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_150,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_36])).

tff(c_252,plain,(
    ! [A_41,B_42] : r1_xboole_0(k4_xboole_0(A_41,B_42),k4_xboole_0(B_42,A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,(
    ! [B_43] : k4_xboole_0(B_43,B_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_20])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_325,plain,(
    ! [B_44] : r1_tarski(k1_xboole_0,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_14])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_370,plain,(
    ! [B_46] : k3_xboole_0(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_325,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [B_46] : k3_xboole_0(B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_2])).

tff(c_75,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_204,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_204])).

tff(c_587,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),C_63) = k3_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_928,plain,(
    ! [C_80] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_80)) = k4_xboole_0('#skF_1',C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_587])).

tff(c_951,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_928])).

tff(c_955,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_951])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_955])).

tff(c_959,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1028,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1046,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_959,c_1028])).

tff(c_1448,plain,(
    ! [A_116,B_117,C_118] : k4_xboole_0(k3_xboole_0(A_116,B_117),C_118) = k3_xboole_0(A_116,k4_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1964,plain,(
    ! [C_141] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_141)) = k4_xboole_0('#skF_1',C_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_1448])).

tff(c_1047,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1028])).

tff(c_1985,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1964,c_1047])).

tff(c_1221,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_xboole_0(A_100,k4_xboole_0(C_101,B_102))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1240,plain,(
    ! [C_101,B_102,A_100] :
      ( r1_xboole_0(k4_xboole_0(C_101,B_102),A_100)
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(resolution,[status(thm)],[c_1221,c_4])).

tff(c_2135,plain,(
    ! [A_145] :
      ( r1_xboole_0('#skF_1',A_145)
      | ~ r1_tarski(A_145,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1985,c_1240])).

tff(c_958,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2146,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2135,c_958])).

tff(c_2151,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2146])).

tff(c_2155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.61  
% 3.14/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.61  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.14/1.61  
% 3.14/1.61  %Foreground sorts:
% 3.14/1.61  
% 3.14/1.61  
% 3.14/1.61  %Background operators:
% 3.14/1.61  
% 3.14/1.61  
% 3.14/1.61  %Foreground operators:
% 3.14/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.61  
% 3.14/1.62  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 3.14/1.62  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.14/1.62  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.14/1.62  tff(f_70, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.14/1.62  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.14/1.62  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.14/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.14/1.62  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.14/1.62  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.14/1.62  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.14/1.62  tff(c_999, plain, (![A_87, B_88]: (r1_xboole_0(k4_xboole_0(A_87, B_88), k4_xboole_0(B_88, A_87)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.62  tff(c_20, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.62  tff(c_1008, plain, (![B_88]: (k4_xboole_0(B_88, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_999, c_20])).
% 3.14/1.62  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.62  tff(c_142, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.62  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.62  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 3.14/1.62  tff(c_150, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_36])).
% 3.14/1.62  tff(c_252, plain, (![A_41, B_42]: (r1_xboole_0(k4_xboole_0(A_41, B_42), k4_xboole_0(B_42, A_41)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.62  tff(c_295, plain, (![B_43]: (k4_xboole_0(B_43, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_252, c_20])).
% 3.14/1.62  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.62  tff(c_325, plain, (![B_44]: (r1_tarski(k1_xboole_0, B_44))), inference(superposition, [status(thm), theory('equality')], [c_295, c_14])).
% 3.14/1.62  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.62  tff(c_370, plain, (![B_46]: (k3_xboole_0(k1_xboole_0, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_325, c_12])).
% 3.14/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.62  tff(c_375, plain, (![B_46]: (k3_xboole_0(B_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_370, c_2])).
% 3.14/1.62  tff(c_75, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.62  tff(c_83, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_75])).
% 3.14/1.62  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.62  tff(c_204, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.62  tff(c_227, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_204])).
% 3.14/1.62  tff(c_587, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), C_63)=k3_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.62  tff(c_928, plain, (![C_80]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_80))=k4_xboole_0('#skF_1', C_80))), inference(superposition, [status(thm), theory('equality')], [c_227, c_587])).
% 3.14/1.62  tff(c_951, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_928])).
% 3.14/1.62  tff(c_955, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_375, c_951])).
% 3.14/1.62  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_955])).
% 3.14/1.62  tff(c_959, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 3.14/1.62  tff(c_1028, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.62  tff(c_1046, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_959, c_1028])).
% 3.14/1.62  tff(c_1448, plain, (![A_116, B_117, C_118]: (k4_xboole_0(k3_xboole_0(A_116, B_117), C_118)=k3_xboole_0(A_116, k4_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.62  tff(c_1964, plain, (![C_141]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_141))=k4_xboole_0('#skF_1', C_141))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_1448])).
% 3.14/1.62  tff(c_1047, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1028])).
% 3.14/1.62  tff(c_1985, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1964, c_1047])).
% 3.14/1.62  tff(c_1221, plain, (![A_100, C_101, B_102]: (r1_xboole_0(A_100, k4_xboole_0(C_101, B_102)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.62  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.62  tff(c_1240, plain, (![C_101, B_102, A_100]: (r1_xboole_0(k4_xboole_0(C_101, B_102), A_100) | ~r1_tarski(A_100, B_102))), inference(resolution, [status(thm)], [c_1221, c_4])).
% 3.14/1.62  tff(c_2135, plain, (![A_145]: (r1_xboole_0('#skF_1', A_145) | ~r1_tarski(A_145, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1985, c_1240])).
% 3.14/1.62  tff(c_958, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 3.14/1.62  tff(c_2146, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2135, c_958])).
% 3.14/1.62  tff(c_2151, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2146])).
% 3.14/1.62  tff(c_2155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2151])).
% 3.14/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.62  
% 3.14/1.62  Inference rules
% 3.14/1.62  ----------------------
% 3.14/1.62  #Ref     : 0
% 3.14/1.62  #Sup     : 542
% 3.14/1.62  #Fact    : 0
% 3.14/1.62  #Define  : 0
% 3.14/1.62  #Split   : 2
% 3.14/1.62  #Chain   : 0
% 3.14/1.62  #Close   : 0
% 3.14/1.62  
% 3.14/1.62  Ordering : KBO
% 3.14/1.62  
% 3.14/1.62  Simplification rules
% 3.14/1.63  ----------------------
% 3.14/1.63  #Subsume      : 11
% 3.14/1.63  #Demod        : 350
% 3.14/1.63  #Tautology    : 398
% 3.14/1.63  #SimpNegUnit  : 2
% 3.14/1.63  #BackRed      : 2
% 3.14/1.63  
% 3.14/1.63  #Partial instantiations: 0
% 3.14/1.63  #Strategies tried      : 1
% 3.14/1.63  
% 3.14/1.63  Timing (in seconds)
% 3.14/1.63  ----------------------
% 3.14/1.63  Preprocessing        : 0.31
% 3.14/1.63  Parsing              : 0.17
% 3.14/1.63  CNF conversion       : 0.02
% 3.14/1.63  Main loop            : 0.50
% 3.14/1.63  Inferencing          : 0.17
% 3.14/1.63  Reduction            : 0.19
% 3.14/1.63  Demodulation         : 0.15
% 3.14/1.63  BG Simplification    : 0.02
% 3.14/1.63  Subsumption          : 0.08
% 3.14/1.63  Abstraction          : 0.02
% 3.14/1.63  MUC search           : 0.00
% 3.51/1.63  Cooper               : 0.00
% 3.51/1.63  Total                : 0.84
% 3.51/1.63  Index Insertion      : 0.00
% 3.51/1.63  Index Deletion       : 0.00
% 3.51/1.63  Index Matching       : 0.00
% 3.51/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
