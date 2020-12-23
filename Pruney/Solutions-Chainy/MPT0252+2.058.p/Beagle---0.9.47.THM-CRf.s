%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:08 EST 2020

% Result     : Theorem 17.30s
% Output     : CNFRefutation 17.30s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 167 expanded)
%              Number of leaves         :   32 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 172 expanded)
%              Number of equality atoms :   32 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_409,plain,(
    ! [D_120,C_121,B_122,A_123] : k2_enumset1(D_120,C_121,B_122,A_123) = k2_enumset1(A_123,B_122,C_121,D_120) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_425,plain,(
    ! [D_120,C_121,B_122] : k2_enumset1(D_120,C_121,B_122,B_122) = k1_enumset1(B_122,C_121,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_34])).

tff(c_36,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_47,E_51,D_50,C_49,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,D_50,E_51) = k3_enumset1(A_47,B_48,C_49,D_50,E_51) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1518,plain,(
    ! [B_166,E_165,C_163,D_167,A_168,F_164] : k2_xboole_0(k3_enumset1(A_168,B_166,C_163,D_167,E_165),k1_tarski(F_164)) = k4_enumset1(A_168,B_166,C_163,D_167,E_165,F_164) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1536,plain,(
    ! [D_46,C_45,A_43,B_44,F_164] : k4_enumset1(A_43,A_43,B_44,C_45,D_46,F_164) = k2_xboole_0(k2_enumset1(A_43,B_44,C_45,D_46),k1_tarski(F_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1518])).

tff(c_8665,plain,(
    ! [B_254,D_251,C_250,A_253,F_252] : k2_xboole_0(k2_enumset1(A_253,B_254,C_250,D_251),k1_tarski(F_252)) = k3_enumset1(A_253,B_254,C_250,D_251,F_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1536])).

tff(c_8719,plain,(
    ! [A_40,B_41,C_42,F_252] : k3_enumset1(A_40,A_40,B_41,C_42,F_252) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(F_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8665])).

tff(c_34840,plain,(
    ! [A_384,B_385,C_386,F_387] : k2_xboole_0(k1_enumset1(A_384,B_385,C_386),k1_tarski(F_387)) = k2_enumset1(A_384,B_385,C_386,F_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8719])).

tff(c_35784,plain,(
    ! [A_415,B_416,C_417,F_418] : r1_tarski(k1_enumset1(A_415,B_416,C_417),k2_enumset1(A_415,B_416,C_417,F_418)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34840,c_16])).

tff(c_35795,plain,(
    ! [D_120,C_121,B_122] : r1_tarski(k1_enumset1(D_120,C_121,B_122),k1_enumset1(B_122,C_121,D_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_35784])).

tff(c_36536,plain,(
    ! [D_421,C_422,B_423] : r1_tarski(k1_enumset1(D_421,C_422,B_423),k1_enumset1(B_423,C_422,D_421)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_35784])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36538,plain,(
    ! [D_421,C_422,B_423] :
      ( k1_enumset1(D_421,C_422,B_423) = k1_enumset1(B_423,C_422,D_421)
      | ~ r1_tarski(k1_enumset1(B_423,C_422,D_421),k1_enumset1(D_421,C_422,B_423)) ) ),
    inference(resolution,[status(thm)],[c_36536,c_8])).

tff(c_36565,plain,(
    ! [D_424,C_425,B_426] : k1_enumset1(D_424,C_425,B_426) = k1_enumset1(B_426,C_425,D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35795,c_36538])).

tff(c_32,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36647,plain,(
    ! [D_424,C_425] : k1_enumset1(D_424,C_425,C_425) = k2_tarski(C_425,D_424) ),
    inference(superposition,[status(thm),theory(equality)],[c_36565,c_32])).

tff(c_1728,plain,(
    ! [D_186,C_187,B_188] : k2_enumset1(D_186,C_187,B_188,B_188) = k1_enumset1(B_188,C_187,D_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_34])).

tff(c_1741,plain,(
    ! [C_187,B_188] : k1_enumset1(C_187,B_188,B_188) = k1_enumset1(B_188,C_187,C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_34])).

tff(c_36798,plain,(
    ! [C_432,B_433] : k2_tarski(C_432,B_433) = k2_tarski(B_433,C_432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36647,c_36647,c_1741])).

tff(c_44,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37037,plain,(
    ! [B_440,C_441] : k3_tarski(k2_tarski(B_440,C_441)) = k2_xboole_0(C_441,B_440) ),
    inference(superposition,[status(thm),theory(equality)],[c_36798,c_44])).

tff(c_37043,plain,(
    ! [C_441,B_440] : k2_xboole_0(C_441,B_440) = k2_xboole_0(B_440,C_441) ),
    inference(superposition,[status(thm),theory(equality)],[c_37037,c_44])).

tff(c_54,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_165,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_165])).

tff(c_219,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_37067,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37043,c_219])).

tff(c_37071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_37067])).

tff(c_37072,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_37079,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37072,c_16])).

tff(c_50,plain,(
    ! [A_67,C_69,B_68] :
      ( r2_hidden(A_67,C_69)
      | ~ r1_tarski(k2_tarski(A_67,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_37085,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_37079,c_50])).

tff(c_37094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_37085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.30/10.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.30/10.15  
% 17.30/10.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.30/10.15  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 17.30/10.15  
% 17.30/10.15  %Foreground sorts:
% 17.30/10.15  
% 17.30/10.15  
% 17.30/10.15  %Background operators:
% 17.30/10.15  
% 17.30/10.15  
% 17.30/10.15  %Foreground operators:
% 17.30/10.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.30/10.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.30/10.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.30/10.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.30/10.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.30/10.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.30/10.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.30/10.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.30/10.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.30/10.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.30/10.15  tff('#skF_2', type, '#skF_2': $i).
% 17.30/10.15  tff('#skF_3', type, '#skF_3': $i).
% 17.30/10.15  tff('#skF_1', type, '#skF_1': $i).
% 17.30/10.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.30/10.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.30/10.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.30/10.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.30/10.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.30/10.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.30/10.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.30/10.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.30/10.15  
% 17.30/10.17  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 17.30/10.17  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.30/10.17  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 17.30/10.17  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 17.30/10.17  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 17.30/10.17  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 17.30/10.17  tff(f_51, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 17.30/10.17  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.30/10.17  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 17.30/10.17  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.30/10.17  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 17.30/10.17  tff(c_52, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.30/10.17  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.30/10.17  tff(c_409, plain, (![D_120, C_121, B_122, A_123]: (k2_enumset1(D_120, C_121, B_122, A_123)=k2_enumset1(A_123, B_122, C_121, D_120))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.30/10.17  tff(c_34, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.30/10.17  tff(c_425, plain, (![D_120, C_121, B_122]: (k2_enumset1(D_120, C_121, B_122, B_122)=k1_enumset1(B_122, C_121, D_120))), inference(superposition, [status(thm), theory('equality')], [c_409, c_34])).
% 17.30/10.17  tff(c_36, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.30/10.17  tff(c_38, plain, (![A_47, E_51, D_50, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, E_51)=k3_enumset1(A_47, B_48, C_49, D_50, E_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.30/10.17  tff(c_1518, plain, (![B_166, E_165, C_163, D_167, A_168, F_164]: (k2_xboole_0(k3_enumset1(A_168, B_166, C_163, D_167, E_165), k1_tarski(F_164))=k4_enumset1(A_168, B_166, C_163, D_167, E_165, F_164))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.30/10.17  tff(c_1536, plain, (![D_46, C_45, A_43, B_44, F_164]: (k4_enumset1(A_43, A_43, B_44, C_45, D_46, F_164)=k2_xboole_0(k2_enumset1(A_43, B_44, C_45, D_46), k1_tarski(F_164)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1518])).
% 17.30/10.17  tff(c_8665, plain, (![B_254, D_251, C_250, A_253, F_252]: (k2_xboole_0(k2_enumset1(A_253, B_254, C_250, D_251), k1_tarski(F_252))=k3_enumset1(A_253, B_254, C_250, D_251, F_252))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1536])).
% 17.30/10.17  tff(c_8719, plain, (![A_40, B_41, C_42, F_252]: (k3_enumset1(A_40, A_40, B_41, C_42, F_252)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(F_252)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_8665])).
% 17.30/10.17  tff(c_34840, plain, (![A_384, B_385, C_386, F_387]: (k2_xboole_0(k1_enumset1(A_384, B_385, C_386), k1_tarski(F_387))=k2_enumset1(A_384, B_385, C_386, F_387))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8719])).
% 17.30/10.17  tff(c_35784, plain, (![A_415, B_416, C_417, F_418]: (r1_tarski(k1_enumset1(A_415, B_416, C_417), k2_enumset1(A_415, B_416, C_417, F_418)))), inference(superposition, [status(thm), theory('equality')], [c_34840, c_16])).
% 17.30/10.17  tff(c_35795, plain, (![D_120, C_121, B_122]: (r1_tarski(k1_enumset1(D_120, C_121, B_122), k1_enumset1(B_122, C_121, D_120)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_35784])).
% 17.30/10.17  tff(c_36536, plain, (![D_421, C_422, B_423]: (r1_tarski(k1_enumset1(D_421, C_422, B_423), k1_enumset1(B_423, C_422, D_421)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_35784])).
% 17.30/10.17  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.30/10.17  tff(c_36538, plain, (![D_421, C_422, B_423]: (k1_enumset1(D_421, C_422, B_423)=k1_enumset1(B_423, C_422, D_421) | ~r1_tarski(k1_enumset1(B_423, C_422, D_421), k1_enumset1(D_421, C_422, B_423)))), inference(resolution, [status(thm)], [c_36536, c_8])).
% 17.30/10.17  tff(c_36565, plain, (![D_424, C_425, B_426]: (k1_enumset1(D_424, C_425, B_426)=k1_enumset1(B_426, C_425, D_424))), inference(demodulation, [status(thm), theory('equality')], [c_35795, c_36538])).
% 17.30/10.17  tff(c_32, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.30/10.17  tff(c_36647, plain, (![D_424, C_425]: (k1_enumset1(D_424, C_425, C_425)=k2_tarski(C_425, D_424))), inference(superposition, [status(thm), theory('equality')], [c_36565, c_32])).
% 17.30/10.17  tff(c_1728, plain, (![D_186, C_187, B_188]: (k2_enumset1(D_186, C_187, B_188, B_188)=k1_enumset1(B_188, C_187, D_186))), inference(superposition, [status(thm), theory('equality')], [c_409, c_34])).
% 17.30/10.17  tff(c_1741, plain, (![C_187, B_188]: (k1_enumset1(C_187, B_188, B_188)=k1_enumset1(B_188, C_187, C_187))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_34])).
% 17.30/10.17  tff(c_36798, plain, (![C_432, B_433]: (k2_tarski(C_432, B_433)=k2_tarski(B_433, C_432))), inference(demodulation, [status(thm), theory('equality')], [c_36647, c_36647, c_1741])).
% 17.30/10.17  tff(c_44, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.30/10.17  tff(c_37037, plain, (![B_440, C_441]: (k3_tarski(k2_tarski(B_440, C_441))=k2_xboole_0(C_441, B_440))), inference(superposition, [status(thm), theory('equality')], [c_36798, c_44])).
% 17.30/10.17  tff(c_37043, plain, (![C_441, B_440]: (k2_xboole_0(C_441, B_440)=k2_xboole_0(B_440, C_441))), inference(superposition, [status(thm), theory('equality')], [c_37037, c_44])).
% 17.30/10.17  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.30/10.17  tff(c_165, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.30/10.17  tff(c_174, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_165])).
% 17.30/10.17  tff(c_219, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_174])).
% 17.30/10.17  tff(c_37067, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_37043, c_219])).
% 17.30/10.17  tff(c_37071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_37067])).
% 17.30/10.17  tff(c_37072, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_174])).
% 17.30/10.17  tff(c_37079, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37072, c_16])).
% 17.30/10.17  tff(c_50, plain, (![A_67, C_69, B_68]: (r2_hidden(A_67, C_69) | ~r1_tarski(k2_tarski(A_67, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.30/10.17  tff(c_37085, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_37079, c_50])).
% 17.30/10.17  tff(c_37094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_37085])).
% 17.30/10.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.30/10.17  
% 17.30/10.17  Inference rules
% 17.30/10.17  ----------------------
% 17.30/10.17  #Ref     : 0
% 17.30/10.17  #Sup     : 9829
% 17.30/10.17  #Fact    : 0
% 17.30/10.17  #Define  : 0
% 17.30/10.17  #Split   : 1
% 17.30/10.17  #Chain   : 0
% 17.30/10.17  #Close   : 0
% 17.30/10.17  
% 17.30/10.17  Ordering : KBO
% 17.30/10.17  
% 17.30/10.17  Simplification rules
% 17.30/10.17  ----------------------
% 17.30/10.17  #Subsume      : 667
% 17.30/10.17  #Demod        : 13544
% 17.30/10.17  #Tautology    : 3280
% 17.30/10.17  #SimpNegUnit  : 1
% 17.30/10.17  #BackRed      : 8
% 17.30/10.17  
% 17.30/10.17  #Partial instantiations: 0
% 17.30/10.17  #Strategies tried      : 1
% 17.30/10.17  
% 17.30/10.17  Timing (in seconds)
% 17.30/10.17  ----------------------
% 17.30/10.17  Preprocessing        : 0.35
% 17.30/10.17  Parsing              : 0.19
% 17.30/10.17  CNF conversion       : 0.02
% 17.30/10.17  Main loop            : 9.02
% 17.30/10.17  Inferencing          : 1.12
% 17.30/10.17  Reduction            : 6.55
% 17.30/10.17  Demodulation         : 6.25
% 17.30/10.17  BG Simplification    : 0.20
% 17.30/10.17  Subsumption          : 0.91
% 17.30/10.17  Abstraction          : 0.32
% 17.30/10.17  MUC search           : 0.00
% 17.30/10.17  Cooper               : 0.00
% 17.30/10.17  Total                : 9.40
% 17.30/10.17  Index Insertion      : 0.00
% 17.30/10.17  Index Deletion       : 0.00
% 17.30/10.17  Index Matching       : 0.00
% 17.30/10.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
