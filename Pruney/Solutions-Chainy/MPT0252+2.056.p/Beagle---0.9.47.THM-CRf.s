%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:08 EST 2020

% Result     : Theorem 16.10s
% Output     : CNFRefutation 16.18s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 166 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 172 expanded)
%              Number of equality atoms :   30 ( 104 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_78,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

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

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_486,plain,(
    ! [D_115,C_116,B_117,A_118] : k2_enumset1(D_115,C_116,B_117,A_118) = k2_enumset1(A_118,B_117,C_116,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_521,plain,(
    ! [C_41,B_40,A_39] : k2_enumset1(C_41,B_40,A_39,A_39) = k1_enumset1(A_39,B_40,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_486])).

tff(c_36,plain,(
    ! [A_42,B_43,C_44,D_45] : k3_enumset1(A_42,A_42,B_43,C_44,D_45) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_46,E_50,B_47,C_48,D_49] : k4_enumset1(A_46,A_46,B_47,C_48,D_49,E_50) = k3_enumset1(A_46,B_47,C_48,D_49,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1258,plain,(
    ! [C_151,A_156,D_155,E_153,F_152,B_154] : k2_xboole_0(k3_enumset1(A_156,B_154,C_151,D_155,E_153),k1_tarski(F_152)) = k4_enumset1(A_156,B_154,C_151,D_155,E_153,F_152) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1276,plain,(
    ! [B_43,A_42,D_45,C_44,F_152] : k4_enumset1(A_42,A_42,B_43,C_44,D_45,F_152) = k2_xboole_0(k2_enumset1(A_42,B_43,C_44,D_45),k1_tarski(F_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1258])).

tff(c_8321,plain,(
    ! [D_231,A_233,B_232,F_234,C_235] : k2_xboole_0(k2_enumset1(A_233,B_232,C_235,D_231),k1_tarski(F_234)) = k3_enumset1(A_233,B_232,C_235,D_231,F_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1276])).

tff(c_28918,plain,(
    ! [B_357,F_355,C_354,A_356,D_353] : r1_tarski(k2_enumset1(A_356,B_357,C_354,D_353),k3_enumset1(A_356,B_357,C_354,D_353,F_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8321,c_16])).

tff(c_28935,plain,(
    ! [A_39,B_40,C_41,F_355] : r1_tarski(k1_enumset1(A_39,B_40,C_41),k3_enumset1(A_39,A_39,B_40,C_41,F_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_28918])).

tff(c_30003,plain,(
    ! [A_361,B_362,C_363,F_364] : r1_tarski(k1_enumset1(A_361,B_362,C_363),k2_enumset1(A_361,B_362,C_363,F_364)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28935])).

tff(c_30014,plain,(
    ! [C_41,B_40,A_39] : r1_tarski(k1_enumset1(C_41,B_40,A_39),k1_enumset1(A_39,B_40,C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_30003])).

tff(c_30137,plain,(
    ! [C_378,B_379,A_380] : r1_tarski(k1_enumset1(C_378,B_379,A_380),k1_enumset1(A_380,B_379,C_378)) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_30003])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30139,plain,(
    ! [C_378,B_379,A_380] :
      ( k1_enumset1(C_378,B_379,A_380) = k1_enumset1(A_380,B_379,C_378)
      | ~ r1_tarski(k1_enumset1(A_380,B_379,C_378),k1_enumset1(C_378,B_379,A_380)) ) ),
    inference(resolution,[status(thm)],[c_30137,c_8])).

tff(c_30166,plain,(
    ! [C_381,B_382,A_383] : k1_enumset1(C_381,B_382,A_383) = k1_enumset1(A_383,B_382,C_381) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30014,c_30139])).

tff(c_30273,plain,(
    ! [B_38,A_37] : k1_enumset1(B_38,A_37,A_37) = k2_tarski(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_30166])).

tff(c_1814,plain,(
    ! [C_172,B_173,A_174] : k2_enumset1(C_172,B_173,A_174,A_174) = k1_enumset1(A_174,B_173,C_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_486])).

tff(c_1827,plain,(
    ! [B_173,A_174] : k1_enumset1(B_173,A_174,A_174) = k1_enumset1(A_174,B_173,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_34])).

tff(c_30962,plain,(
    ! [B_391,A_392] : k2_tarski(B_391,A_392) = k2_tarski(A_392,B_391) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30273,c_30273,c_1827])).

tff(c_42,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_31775,plain,(
    ! [A_399,B_400] : k3_tarski(k2_tarski(A_399,B_400)) = k2_xboole_0(B_400,A_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_30962,c_42])).

tff(c_31781,plain,(
    ! [B_400,A_399] : k2_xboole_0(B_400,A_399) = k2_xboole_0(A_399,B_400) ),
    inference(superposition,[status(thm),theory(equality)],[c_31775,c_42])).

tff(c_52,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_181,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(B_83,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_181])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_31804,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31781,c_216])).

tff(c_31809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_31804])).

tff(c_31810,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_31817,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31810,c_16])).

tff(c_48,plain,(
    ! [A_59,C_61,B_60] :
      ( r2_hidden(A_59,C_61)
      | ~ r1_tarski(k2_tarski(A_59,B_60),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_31825,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_31817,c_48])).

tff(c_31830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_31825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.10/8.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.10/8.88  
% 16.10/8.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.10/8.89  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 16.10/8.89  
% 16.10/8.89  %Foreground sorts:
% 16.10/8.89  
% 16.10/8.89  
% 16.10/8.89  %Background operators:
% 16.10/8.89  
% 16.10/8.89  
% 16.10/8.89  %Foreground operators:
% 16.10/8.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.10/8.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.10/8.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.10/8.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.10/8.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.10/8.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.10/8.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.10/8.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.10/8.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.10/8.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.10/8.89  tff('#skF_2', type, '#skF_2': $i).
% 16.10/8.89  tff('#skF_3', type, '#skF_3': $i).
% 16.10/8.89  tff('#skF_1', type, '#skF_1': $i).
% 16.10/8.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.10/8.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.10/8.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.10/8.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.10/8.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.10/8.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.10/8.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.10/8.89  
% 16.18/8.90  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 16.18/8.90  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.18/8.90  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 16.18/8.90  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 16.18/8.90  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 16.18/8.90  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 16.18/8.90  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 16.18/8.90  tff(f_51, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 16.18/8.90  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.18/8.90  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.18/8.90  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 16.18/8.90  tff(c_50, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.18/8.90  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.18/8.90  tff(c_32, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.18/8.90  tff(c_34, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.18/8.90  tff(c_486, plain, (![D_115, C_116, B_117, A_118]: (k2_enumset1(D_115, C_116, B_117, A_118)=k2_enumset1(A_118, B_117, C_116, D_115))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.18/8.90  tff(c_521, plain, (![C_41, B_40, A_39]: (k2_enumset1(C_41, B_40, A_39, A_39)=k1_enumset1(A_39, B_40, C_41))), inference(superposition, [status(thm), theory('equality')], [c_34, c_486])).
% 16.18/8.90  tff(c_36, plain, (![A_42, B_43, C_44, D_45]: (k3_enumset1(A_42, A_42, B_43, C_44, D_45)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.18/8.90  tff(c_38, plain, (![A_46, E_50, B_47, C_48, D_49]: (k4_enumset1(A_46, A_46, B_47, C_48, D_49, E_50)=k3_enumset1(A_46, B_47, C_48, D_49, E_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.18/8.90  tff(c_1258, plain, (![C_151, A_156, D_155, E_153, F_152, B_154]: (k2_xboole_0(k3_enumset1(A_156, B_154, C_151, D_155, E_153), k1_tarski(F_152))=k4_enumset1(A_156, B_154, C_151, D_155, E_153, F_152))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.18/8.90  tff(c_1276, plain, (![B_43, A_42, D_45, C_44, F_152]: (k4_enumset1(A_42, A_42, B_43, C_44, D_45, F_152)=k2_xboole_0(k2_enumset1(A_42, B_43, C_44, D_45), k1_tarski(F_152)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1258])).
% 16.18/8.90  tff(c_8321, plain, (![D_231, A_233, B_232, F_234, C_235]: (k2_xboole_0(k2_enumset1(A_233, B_232, C_235, D_231), k1_tarski(F_234))=k3_enumset1(A_233, B_232, C_235, D_231, F_234))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1276])).
% 16.18/8.90  tff(c_28918, plain, (![B_357, F_355, C_354, A_356, D_353]: (r1_tarski(k2_enumset1(A_356, B_357, C_354, D_353), k3_enumset1(A_356, B_357, C_354, D_353, F_355)))), inference(superposition, [status(thm), theory('equality')], [c_8321, c_16])).
% 16.18/8.90  tff(c_28935, plain, (![A_39, B_40, C_41, F_355]: (r1_tarski(k1_enumset1(A_39, B_40, C_41), k3_enumset1(A_39, A_39, B_40, C_41, F_355)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_28918])).
% 16.18/8.90  tff(c_30003, plain, (![A_361, B_362, C_363, F_364]: (r1_tarski(k1_enumset1(A_361, B_362, C_363), k2_enumset1(A_361, B_362, C_363, F_364)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28935])).
% 16.18/8.90  tff(c_30014, plain, (![C_41, B_40, A_39]: (r1_tarski(k1_enumset1(C_41, B_40, A_39), k1_enumset1(A_39, B_40, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_521, c_30003])).
% 16.18/8.90  tff(c_30137, plain, (![C_378, B_379, A_380]: (r1_tarski(k1_enumset1(C_378, B_379, A_380), k1_enumset1(A_380, B_379, C_378)))), inference(superposition, [status(thm), theory('equality')], [c_521, c_30003])).
% 16.18/8.90  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.18/8.90  tff(c_30139, plain, (![C_378, B_379, A_380]: (k1_enumset1(C_378, B_379, A_380)=k1_enumset1(A_380, B_379, C_378) | ~r1_tarski(k1_enumset1(A_380, B_379, C_378), k1_enumset1(C_378, B_379, A_380)))), inference(resolution, [status(thm)], [c_30137, c_8])).
% 16.18/8.90  tff(c_30166, plain, (![C_381, B_382, A_383]: (k1_enumset1(C_381, B_382, A_383)=k1_enumset1(A_383, B_382, C_381))), inference(demodulation, [status(thm), theory('equality')], [c_30014, c_30139])).
% 16.18/8.90  tff(c_30273, plain, (![B_38, A_37]: (k1_enumset1(B_38, A_37, A_37)=k2_tarski(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_32, c_30166])).
% 16.18/8.90  tff(c_1814, plain, (![C_172, B_173, A_174]: (k2_enumset1(C_172, B_173, A_174, A_174)=k1_enumset1(A_174, B_173, C_172))), inference(superposition, [status(thm), theory('equality')], [c_34, c_486])).
% 16.18/8.90  tff(c_1827, plain, (![B_173, A_174]: (k1_enumset1(B_173, A_174, A_174)=k1_enumset1(A_174, B_173, B_173))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_34])).
% 16.18/8.90  tff(c_30962, plain, (![B_391, A_392]: (k2_tarski(B_391, A_392)=k2_tarski(A_392, B_391))), inference(demodulation, [status(thm), theory('equality')], [c_30273, c_30273, c_1827])).
% 16.18/8.90  tff(c_42, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.18/8.90  tff(c_31775, plain, (![A_399, B_400]: (k3_tarski(k2_tarski(A_399, B_400))=k2_xboole_0(B_400, A_399))), inference(superposition, [status(thm), theory('equality')], [c_30962, c_42])).
% 16.18/8.90  tff(c_31781, plain, (![B_400, A_399]: (k2_xboole_0(B_400, A_399)=k2_xboole_0(A_399, B_400))), inference(superposition, [status(thm), theory('equality')], [c_31775, c_42])).
% 16.18/8.90  tff(c_52, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.18/8.90  tff(c_181, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(B_83, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.18/8.90  tff(c_190, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_181])).
% 16.18/8.90  tff(c_216, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_190])).
% 16.18/8.90  tff(c_31804, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_31781, c_216])).
% 16.18/8.90  tff(c_31809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_31804])).
% 16.18/8.90  tff(c_31810, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_190])).
% 16.18/8.90  tff(c_31817, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31810, c_16])).
% 16.18/8.90  tff(c_48, plain, (![A_59, C_61, B_60]: (r2_hidden(A_59, C_61) | ~r1_tarski(k2_tarski(A_59, B_60), C_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.18/8.90  tff(c_31825, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_31817, c_48])).
% 16.18/8.90  tff(c_31830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_31825])).
% 16.18/8.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.18/8.90  
% 16.18/8.90  Inference rules
% 16.18/8.90  ----------------------
% 16.18/8.90  #Ref     : 0
% 16.18/8.90  #Sup     : 8487
% 16.18/8.90  #Fact    : 0
% 16.18/8.90  #Define  : 0
% 16.18/8.90  #Split   : 1
% 16.18/8.90  #Chain   : 0
% 16.18/8.90  #Close   : 0
% 16.18/8.90  
% 16.18/8.90  Ordering : KBO
% 16.18/8.90  
% 16.18/8.90  Simplification rules
% 16.18/8.90  ----------------------
% 16.18/8.90  #Subsume      : 557
% 16.18/8.90  #Demod        : 9792
% 16.18/8.90  #Tautology    : 2604
% 16.18/8.90  #SimpNegUnit  : 1
% 16.18/8.90  #BackRed      : 9
% 16.18/8.90  
% 16.18/8.90  #Partial instantiations: 0
% 16.18/8.90  #Strategies tried      : 1
% 16.18/8.90  
% 16.18/8.90  Timing (in seconds)
% 16.18/8.90  ----------------------
% 16.18/8.90  Preprocessing        : 0.32
% 16.18/8.91  Parsing              : 0.17
% 16.18/8.91  CNF conversion       : 0.02
% 16.18/8.91  Main loop            : 7.83
% 16.18/8.91  Inferencing          : 0.95
% 16.18/8.91  Reduction            : 5.65
% 16.18/8.91  Demodulation         : 5.38
% 16.18/8.91  BG Simplification    : 0.18
% 16.18/8.91  Subsumption          : 0.84
% 16.18/8.91  Abstraction          : 0.27
% 16.18/8.91  MUC search           : 0.00
% 16.18/8.91  Cooper               : 0.00
% 16.18/8.91  Total                : 8.18
% 16.18/8.91  Index Insertion      : 0.00
% 16.18/8.91  Index Deletion       : 0.00
% 16.18/8.91  Index Matching       : 0.00
% 16.18/8.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
