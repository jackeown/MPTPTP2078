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
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 142 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 150 expanded)
%              Number of equality atoms :   30 ( 103 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_324,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k4_xboole_0(A_55,B_56),C_57) = k4_xboole_0(A_55,k2_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_355,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(B_56,k1_xboole_0)) = k4_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_12])).

tff(c_20,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_414,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,k1_xboole_0)) = k4_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_12])).

tff(c_472,plain,(
    ! [A_60,B_11] : k4_xboole_0(A_60,k4_xboole_0(k1_xboole_0,B_11)) = k4_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_414])).

tff(c_491,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(k1_xboole_0,B_63)) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_472])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_528,plain,(
    ! [B_63] : k3_xboole_0(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_16])).

tff(c_79,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k3_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_124,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_12])).

tff(c_148,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k3_xboole_0(A_43,B_44),C_45) = k3_xboole_0(A_43,k4_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [C_45] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,C_45)) = k4_xboole_0(k1_xboole_0,C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_148])).

tff(c_593,plain,(
    ! [C_45] : k4_xboole_0(k1_xboole_0,C_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_178])).

tff(c_100,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_381,plain,(
    ! [A_16,B_17,C_57] : k4_xboole_0(A_16,k2_xboole_0(k4_xboole_0(A_16,B_17),C_57)) = k4_xboole_0(k3_xboole_0(A_16,B_17),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_324])).

tff(c_1852,plain,(
    ! [A_103,B_104,C_105] : k4_xboole_0(A_103,k2_xboole_0(k4_xboole_0(A_103,B_104),C_105)) = k3_xboole_0(A_103,k4_xboole_0(B_104,C_105)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_381])).

tff(c_1968,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_1852])).

tff(c_2002,plain,(
    ! [A_106,B_107] : k3_xboole_0(A_106,k4_xboole_0(B_107,A_106)) = k3_xboole_0(A_106,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1968])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2843,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,k4_xboole_0(B_123,A_122))
      | ~ r2_hidden(C_124,k3_xboole_0(A_122,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2002,c_6])).

tff(c_2861,plain,(
    ! [C_45,C_124] :
      ( ~ r1_xboole_0(C_45,k1_xboole_0)
      | ~ r2_hidden(C_124,k3_xboole_0(C_45,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_2843])).

tff(c_2880,plain,(
    ! [C_124,C_45] : ~ r2_hidden(C_124,k3_xboole_0(C_45,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2861])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2042,plain,(
    ! [A_106,B_107,C_20] : k3_xboole_0(A_106,k4_xboole_0(k4_xboole_0(B_107,A_106),C_20)) = k4_xboole_0(k3_xboole_0(A_106,k1_xboole_0),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2002,c_18])).

tff(c_12176,plain,(
    ! [A_303,B_304,C_305] : k3_xboole_0(A_303,k4_xboole_0(B_304,k2_xboole_0(A_303,C_305))) = k3_xboole_0(A_303,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_14,c_18,c_2042])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12380,plain,(
    ! [A_303,B_304,C_305] :
      ( r2_hidden('#skF_1'(A_303,k4_xboole_0(B_304,k2_xboole_0(A_303,C_305))),k3_xboole_0(A_303,k1_xboole_0))
      | r1_xboole_0(A_303,k4_xboole_0(B_304,k2_xboole_0(A_303,C_305))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12176,c_4])).

tff(c_12563,plain,(
    ! [A_306,B_307,C_308] : r1_xboole_0(A_306,k4_xboole_0(B_307,k2_xboole_0(A_306,C_308))) ),
    inference(negUnitSimplification,[status(thm)],[c_2880,c_12380])).

tff(c_12648,plain,(
    ! [B_309,A_310] : r1_xboole_0(B_309,k4_xboole_0(A_310,B_309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_12563])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12717,plain,(
    ! [A_310,B_309] : r1_xboole_0(k4_xboole_0(A_310,B_309),B_309) ),
    inference(resolution,[status(thm)],[c_12648,c_2])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12717,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.68  
% 7.46/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.46/2.69  
% 7.46/2.69  %Foreground sorts:
% 7.46/2.69  
% 7.46/2.69  
% 7.46/2.69  %Background operators:
% 7.46/2.69  
% 7.46/2.69  
% 7.46/2.69  %Foreground operators:
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.46/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.46/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.46/2.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.46/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.46/2.69  tff('#skF_3', type, '#skF_3': $i).
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.46/2.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.46/2.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.46/2.69  
% 7.46/2.71  tff(f_53, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.46/2.71  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.46/2.71  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.46/2.71  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.46/2.71  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.46/2.71  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.46/2.71  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.46/2.71  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.46/2.71  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.46/2.71  tff(f_62, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.46/2.71  tff(c_324, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k4_xboole_0(A_55, B_56), C_57)=k4_xboole_0(A_55, k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.46/2.71  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.46/2.71  tff(c_355, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(B_56, k1_xboole_0))=k4_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_324, c_12])).
% 7.46/2.71  tff(c_20, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.46/2.71  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.46/2.71  tff(c_47, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.46/2.71  tff(c_55, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_10, c_47])).
% 7.46/2.71  tff(c_414, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, k1_xboole_0))=k4_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_324, c_12])).
% 7.46/2.71  tff(c_472, plain, (![A_60, B_11]: (k4_xboole_0(A_60, k4_xboole_0(k1_xboole_0, B_11))=k4_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_55, c_414])).
% 7.46/2.71  tff(c_491, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(k1_xboole_0, B_63))=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_472])).
% 7.46/2.71  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.46/2.71  tff(c_528, plain, (![B_63]: (k3_xboole_0(k1_xboole_0, B_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_491, c_16])).
% 7.46/2.71  tff(c_79, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.46/2.71  tff(c_108, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k3_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 7.46/2.71  tff(c_124, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_12])).
% 7.46/2.71  tff(c_148, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k3_xboole_0(A_43, B_44), C_45)=k3_xboole_0(A_43, k4_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.46/2.71  tff(c_178, plain, (![C_45]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, C_45))=k4_xboole_0(k1_xboole_0, C_45))), inference(superposition, [status(thm), theory('equality')], [c_124, c_148])).
% 7.46/2.71  tff(c_593, plain, (![C_45]: (k4_xboole_0(k1_xboole_0, C_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_528, c_178])).
% 7.46/2.71  tff(c_100, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 7.46/2.71  tff(c_18, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.46/2.71  tff(c_381, plain, (![A_16, B_17, C_57]: (k4_xboole_0(A_16, k2_xboole_0(k4_xboole_0(A_16, B_17), C_57))=k4_xboole_0(k3_xboole_0(A_16, B_17), C_57))), inference(superposition, [status(thm), theory('equality')], [c_16, c_324])).
% 7.46/2.71  tff(c_1852, plain, (![A_103, B_104, C_105]: (k4_xboole_0(A_103, k2_xboole_0(k4_xboole_0(A_103, B_104), C_105))=k3_xboole_0(A_103, k4_xboole_0(B_104, C_105)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_381])).
% 7.46/2.71  tff(c_1968, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_55, c_1852])).
% 7.46/2.71  tff(c_2002, plain, (![A_106, B_107]: (k3_xboole_0(A_106, k4_xboole_0(B_107, A_106))=k3_xboole_0(A_106, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1968])).
% 7.46/2.71  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.46/2.71  tff(c_2843, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, k4_xboole_0(B_123, A_122)) | ~r2_hidden(C_124, k3_xboole_0(A_122, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2002, c_6])).
% 7.46/2.71  tff(c_2861, plain, (![C_45, C_124]: (~r1_xboole_0(C_45, k1_xboole_0) | ~r2_hidden(C_124, k3_xboole_0(C_45, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_593, c_2843])).
% 7.46/2.71  tff(c_2880, plain, (![C_124, C_45]: (~r2_hidden(C_124, k3_xboole_0(C_45, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2861])).
% 7.46/2.71  tff(c_14, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.46/2.71  tff(c_2042, plain, (![A_106, B_107, C_20]: (k3_xboole_0(A_106, k4_xboole_0(k4_xboole_0(B_107, A_106), C_20))=k4_xboole_0(k3_xboole_0(A_106, k1_xboole_0), C_20))), inference(superposition, [status(thm), theory('equality')], [c_2002, c_18])).
% 7.46/2.71  tff(c_12176, plain, (![A_303, B_304, C_305]: (k3_xboole_0(A_303, k4_xboole_0(B_304, k2_xboole_0(A_303, C_305)))=k3_xboole_0(A_303, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_14, c_18, c_2042])).
% 7.46/2.71  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.46/2.71  tff(c_12380, plain, (![A_303, B_304, C_305]: (r2_hidden('#skF_1'(A_303, k4_xboole_0(B_304, k2_xboole_0(A_303, C_305))), k3_xboole_0(A_303, k1_xboole_0)) | r1_xboole_0(A_303, k4_xboole_0(B_304, k2_xboole_0(A_303, C_305))))), inference(superposition, [status(thm), theory('equality')], [c_12176, c_4])).
% 7.46/2.71  tff(c_12563, plain, (![A_306, B_307, C_308]: (r1_xboole_0(A_306, k4_xboole_0(B_307, k2_xboole_0(A_306, C_308))))), inference(negUnitSimplification, [status(thm)], [c_2880, c_12380])).
% 7.46/2.71  tff(c_12648, plain, (![B_309, A_310]: (r1_xboole_0(B_309, k4_xboole_0(A_310, B_309)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_12563])).
% 7.46/2.71  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.46/2.71  tff(c_12717, plain, (![A_310, B_309]: (r1_xboole_0(k4_xboole_0(A_310, B_309), B_309))), inference(resolution, [status(thm)], [c_12648, c_2])).
% 7.46/2.71  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.46/2.71  tff(c_12735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12717, c_22])).
% 7.46/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.71  
% 7.46/2.71  Inference rules
% 7.46/2.71  ----------------------
% 7.46/2.71  #Ref     : 0
% 7.46/2.71  #Sup     : 3161
% 7.46/2.71  #Fact    : 0
% 7.46/2.71  #Define  : 0
% 7.46/2.71  #Split   : 0
% 7.46/2.71  #Chain   : 0
% 7.46/2.71  #Close   : 0
% 7.46/2.71  
% 7.46/2.71  Ordering : KBO
% 7.46/2.71  
% 7.46/2.71  Simplification rules
% 7.46/2.71  ----------------------
% 7.46/2.71  #Subsume      : 33
% 7.46/2.71  #Demod        : 3267
% 7.46/2.71  #Tautology    : 1857
% 7.46/2.71  #SimpNegUnit  : 5
% 7.46/2.71  #BackRed      : 7
% 7.46/2.71  
% 7.46/2.71  #Partial instantiations: 0
% 7.46/2.71  #Strategies tried      : 1
% 7.46/2.71  
% 7.46/2.71  Timing (in seconds)
% 7.46/2.71  ----------------------
% 7.46/2.72  Preprocessing        : 0.29
% 7.46/2.72  Parsing              : 0.16
% 7.46/2.72  CNF conversion       : 0.02
% 7.46/2.72  Main loop            : 1.60
% 7.46/2.72  Inferencing          : 0.42
% 7.46/2.72  Reduction            : 0.76
% 7.46/2.72  Demodulation         : 0.64
% 7.46/2.72  BG Simplification    : 0.05
% 7.46/2.72  Subsumption          : 0.27
% 7.46/2.72  Abstraction          : 0.08
% 7.46/2.72  MUC search           : 0.00
% 7.46/2.72  Cooper               : 0.00
% 7.46/2.72  Total                : 1.94
% 7.46/2.72  Index Insertion      : 0.00
% 7.46/2.72  Index Deletion       : 0.00
% 7.46/2.72  Index Matching       : 0.00
% 7.46/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
