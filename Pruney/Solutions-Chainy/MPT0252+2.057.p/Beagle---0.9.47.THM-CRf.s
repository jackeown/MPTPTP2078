%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:08 EST 2020

% Result     : Theorem 15.88s
% Output     : CNFRefutation 15.98s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 185 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :   61 ( 190 expanded)
%              Number of equality atoms :   29 ( 114 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

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

tff(c_8289,plain,(
    ! [F_242,B_240,C_241,D_239,A_244,E_243] : r1_tarski(k3_enumset1(A_244,B_240,C_241,D_239,E_243),k4_enumset1(A_244,B_240,C_241,D_239,E_243,F_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_16])).

tff(c_8297,plain,(
    ! [F_242,D_46,C_45,A_43,B_44] : r1_tarski(k2_enumset1(A_43,B_44,C_45,D_46),k4_enumset1(A_43,A_43,B_44,C_45,D_46,F_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8289])).

tff(c_29824,plain,(
    ! [D_372,B_374,C_371,F_370,A_373] : r1_tarski(k2_enumset1(A_373,B_374,C_371,D_372),k3_enumset1(A_373,B_374,C_371,D_372,F_370)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8297])).

tff(c_29841,plain,(
    ! [A_40,B_41,C_42,F_370] : r1_tarski(k1_enumset1(A_40,B_41,C_42),k3_enumset1(A_40,A_40,B_41,C_42,F_370)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_29824])).

tff(c_29849,plain,(
    ! [A_375,B_376,C_377,F_378] : r1_tarski(k1_enumset1(A_375,B_376,C_377),k2_enumset1(A_375,B_376,C_377,F_378)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_29841])).

tff(c_29860,plain,(
    ! [D_120,C_121,B_122] : r1_tarski(k1_enumset1(D_120,C_121,B_122),k1_enumset1(B_122,C_121,D_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_29849])).

tff(c_30558,plain,(
    ! [D_394,C_395,B_396] : r1_tarski(k1_enumset1(D_394,C_395,B_396),k1_enumset1(B_396,C_395,D_394)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_29849])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30560,plain,(
    ! [D_394,C_395,B_396] :
      ( k1_enumset1(D_394,C_395,B_396) = k1_enumset1(B_396,C_395,D_394)
      | ~ r1_tarski(k1_enumset1(B_396,C_395,D_394),k1_enumset1(D_394,C_395,B_396)) ) ),
    inference(resolution,[status(thm)],[c_30558,c_8])).

tff(c_30587,plain,(
    ! [D_397,C_398,B_399] : k1_enumset1(D_397,C_398,B_399) = k1_enumset1(B_399,C_398,D_397) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29860,c_30560])).

tff(c_1728,plain,(
    ! [D_186,C_187,B_188] : k2_enumset1(D_186,C_187,B_188,B_188) = k1_enumset1(B_188,C_187,D_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_34])).

tff(c_1741,plain,(
    ! [C_187,B_188] : k1_enumset1(C_187,B_188,B_188) = k1_enumset1(B_188,C_187,C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_34])).

tff(c_30659,plain,(
    ! [D_397,B_399] : k1_enumset1(D_397,D_397,B_399) = k1_enumset1(D_397,B_399,B_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_30587,c_1741])).

tff(c_30728,plain,(
    ! [D_397,B_399] : k1_enumset1(D_397,B_399,B_399) = k2_tarski(D_397,B_399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30659])).

tff(c_30914,plain,(
    ! [C_407,B_408] : k2_tarski(C_407,B_408) = k2_tarski(B_408,C_407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30728,c_30728,c_1741])).

tff(c_44,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32372,plain,(
    ! [B_417,C_418] : k3_tarski(k2_tarski(B_417,C_418)) = k2_xboole_0(C_418,B_417) ),
    inference(superposition,[status(thm),theory(equality)],[c_30914,c_44])).

tff(c_32378,plain,(
    ! [C_418,B_417] : k2_xboole_0(C_418,B_417) = k2_xboole_0(B_417,C_418) ),
    inference(superposition,[status(thm),theory(equality)],[c_32372,c_44])).

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

tff(c_32402,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32378,c_219])).

tff(c_32406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32402])).

tff(c_32407,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_32414,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32407,c_16])).

tff(c_50,plain,(
    ! [A_67,C_69,B_68] :
      ( r2_hidden(A_67,C_69)
      | ~ r1_tarski(k2_tarski(A_67,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32420,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32414,c_50])).

tff(c_32429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_32420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.88/8.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/8.75  
% 15.98/8.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/8.75  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.98/8.75  
% 15.98/8.75  %Foreground sorts:
% 15.98/8.75  
% 15.98/8.75  
% 15.98/8.75  %Background operators:
% 15.98/8.75  
% 15.98/8.75  
% 15.98/8.75  %Foreground operators:
% 15.98/8.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.98/8.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.98/8.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.98/8.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.98/8.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.98/8.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.98/8.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.98/8.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.98/8.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.98/8.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.98/8.75  tff('#skF_2', type, '#skF_2': $i).
% 15.98/8.75  tff('#skF_3', type, '#skF_3': $i).
% 15.98/8.75  tff('#skF_1', type, '#skF_1': $i).
% 15.98/8.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.98/8.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.98/8.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.98/8.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 15.98/8.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.98/8.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.98/8.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.98/8.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.98/8.75  
% 15.98/8.76  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 15.98/8.76  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.98/8.76  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 15.98/8.76  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 15.98/8.76  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 15.98/8.76  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 15.98/8.76  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 15.98/8.76  tff(f_51, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 15.98/8.76  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.98/8.76  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 15.98/8.76  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 15.98/8.76  tff(c_52, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.98/8.76  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.98/8.76  tff(c_32, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.98/8.76  tff(c_409, plain, (![D_120, C_121, B_122, A_123]: (k2_enumset1(D_120, C_121, B_122, A_123)=k2_enumset1(A_123, B_122, C_121, D_120))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.98/8.76  tff(c_34, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.98/8.76  tff(c_425, plain, (![D_120, C_121, B_122]: (k2_enumset1(D_120, C_121, B_122, B_122)=k1_enumset1(B_122, C_121, D_120))), inference(superposition, [status(thm), theory('equality')], [c_409, c_34])).
% 15.98/8.76  tff(c_36, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.98/8.76  tff(c_38, plain, (![A_47, E_51, D_50, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, E_51)=k3_enumset1(A_47, B_48, C_49, D_50, E_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.98/8.76  tff(c_1518, plain, (![B_166, E_165, C_163, D_167, A_168, F_164]: (k2_xboole_0(k3_enumset1(A_168, B_166, C_163, D_167, E_165), k1_tarski(F_164))=k4_enumset1(A_168, B_166, C_163, D_167, E_165, F_164))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.98/8.76  tff(c_8289, plain, (![F_242, B_240, C_241, D_239, A_244, E_243]: (r1_tarski(k3_enumset1(A_244, B_240, C_241, D_239, E_243), k4_enumset1(A_244, B_240, C_241, D_239, E_243, F_242)))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_16])).
% 15.98/8.76  tff(c_8297, plain, (![F_242, D_46, C_45, A_43, B_44]: (r1_tarski(k2_enumset1(A_43, B_44, C_45, D_46), k4_enumset1(A_43, A_43, B_44, C_45, D_46, F_242)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_8289])).
% 15.98/8.76  tff(c_29824, plain, (![D_372, B_374, C_371, F_370, A_373]: (r1_tarski(k2_enumset1(A_373, B_374, C_371, D_372), k3_enumset1(A_373, B_374, C_371, D_372, F_370)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8297])).
% 15.98/8.76  tff(c_29841, plain, (![A_40, B_41, C_42, F_370]: (r1_tarski(k1_enumset1(A_40, B_41, C_42), k3_enumset1(A_40, A_40, B_41, C_42, F_370)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_29824])).
% 15.98/8.76  tff(c_29849, plain, (![A_375, B_376, C_377, F_378]: (r1_tarski(k1_enumset1(A_375, B_376, C_377), k2_enumset1(A_375, B_376, C_377, F_378)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_29841])).
% 15.98/8.76  tff(c_29860, plain, (![D_120, C_121, B_122]: (r1_tarski(k1_enumset1(D_120, C_121, B_122), k1_enumset1(B_122, C_121, D_120)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_29849])).
% 15.98/8.76  tff(c_30558, plain, (![D_394, C_395, B_396]: (r1_tarski(k1_enumset1(D_394, C_395, B_396), k1_enumset1(B_396, C_395, D_394)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_29849])).
% 15.98/8.76  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.98/8.76  tff(c_30560, plain, (![D_394, C_395, B_396]: (k1_enumset1(D_394, C_395, B_396)=k1_enumset1(B_396, C_395, D_394) | ~r1_tarski(k1_enumset1(B_396, C_395, D_394), k1_enumset1(D_394, C_395, B_396)))), inference(resolution, [status(thm)], [c_30558, c_8])).
% 15.98/8.76  tff(c_30587, plain, (![D_397, C_398, B_399]: (k1_enumset1(D_397, C_398, B_399)=k1_enumset1(B_399, C_398, D_397))), inference(demodulation, [status(thm), theory('equality')], [c_29860, c_30560])).
% 15.98/8.76  tff(c_1728, plain, (![D_186, C_187, B_188]: (k2_enumset1(D_186, C_187, B_188, B_188)=k1_enumset1(B_188, C_187, D_186))), inference(superposition, [status(thm), theory('equality')], [c_409, c_34])).
% 15.98/8.76  tff(c_1741, plain, (![C_187, B_188]: (k1_enumset1(C_187, B_188, B_188)=k1_enumset1(B_188, C_187, C_187))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_34])).
% 15.98/8.76  tff(c_30659, plain, (![D_397, B_399]: (k1_enumset1(D_397, D_397, B_399)=k1_enumset1(D_397, B_399, B_399))), inference(superposition, [status(thm), theory('equality')], [c_30587, c_1741])).
% 15.98/8.76  tff(c_30728, plain, (![D_397, B_399]: (k1_enumset1(D_397, B_399, B_399)=k2_tarski(D_397, B_399))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30659])).
% 15.98/8.76  tff(c_30914, plain, (![C_407, B_408]: (k2_tarski(C_407, B_408)=k2_tarski(B_408, C_407))), inference(demodulation, [status(thm), theory('equality')], [c_30728, c_30728, c_1741])).
% 15.98/8.76  tff(c_44, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.98/8.76  tff(c_32372, plain, (![B_417, C_418]: (k3_tarski(k2_tarski(B_417, C_418))=k2_xboole_0(C_418, B_417))), inference(superposition, [status(thm), theory('equality')], [c_30914, c_44])).
% 15.98/8.76  tff(c_32378, plain, (![C_418, B_417]: (k2_xboole_0(C_418, B_417)=k2_xboole_0(B_417, C_418))), inference(superposition, [status(thm), theory('equality')], [c_32372, c_44])).
% 15.98/8.76  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.98/8.76  tff(c_165, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.98/8.76  tff(c_174, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_165])).
% 15.98/8.76  tff(c_219, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_174])).
% 15.98/8.76  tff(c_32402, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32378, c_219])).
% 15.98/8.76  tff(c_32406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_32402])).
% 15.98/8.76  tff(c_32407, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_174])).
% 15.98/8.76  tff(c_32414, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32407, c_16])).
% 15.98/8.76  tff(c_50, plain, (![A_67, C_69, B_68]: (r2_hidden(A_67, C_69) | ~r1_tarski(k2_tarski(A_67, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.98/8.76  tff(c_32420, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32414, c_50])).
% 15.98/8.76  tff(c_32429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_32420])).
% 15.98/8.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/8.76  
% 15.98/8.76  Inference rules
% 15.98/8.76  ----------------------
% 15.98/8.76  #Ref     : 0
% 15.98/8.76  #Sup     : 8592
% 15.98/8.76  #Fact    : 0
% 15.98/8.76  #Define  : 0
% 15.98/8.76  #Split   : 1
% 15.98/8.76  #Chain   : 0
% 15.98/8.76  #Close   : 0
% 15.98/8.77  
% 15.98/8.77  Ordering : KBO
% 15.98/8.77  
% 15.98/8.77  Simplification rules
% 15.98/8.77  ----------------------
% 15.98/8.77  #Subsume      : 554
% 15.98/8.77  #Demod        : 10932
% 15.98/8.77  #Tautology    : 2720
% 15.98/8.77  #SimpNegUnit  : 1
% 15.98/8.77  #BackRed      : 9
% 15.98/8.77  
% 15.98/8.77  #Partial instantiations: 0
% 15.98/8.77  #Strategies tried      : 1
% 15.98/8.77  
% 15.98/8.77  Timing (in seconds)
% 15.98/8.77  ----------------------
% 15.98/8.77  Preprocessing        : 0.34
% 15.98/8.77  Parsing              : 0.18
% 15.98/8.77  CNF conversion       : 0.02
% 15.98/8.77  Main loop            : 7.63
% 15.98/8.77  Inferencing          : 0.96
% 15.98/8.77  Reduction            : 5.51
% 15.98/8.77  Demodulation         : 5.22
% 15.98/8.77  BG Simplification    : 0.18
% 15.98/8.77  Subsumption          : 0.78
% 15.98/8.77  Abstraction          : 0.29
% 15.98/8.77  MUC search           : 0.00
% 15.98/8.77  Cooper               : 0.00
% 15.98/8.77  Total                : 8.01
% 15.98/8.77  Index Insertion      : 0.00
% 15.98/8.77  Index Deletion       : 0.00
% 15.98/8.77  Index Matching       : 0.00
% 15.98/8.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
