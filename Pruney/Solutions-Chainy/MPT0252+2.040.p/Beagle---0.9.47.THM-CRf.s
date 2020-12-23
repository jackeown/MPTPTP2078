%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:06 EST 2020

% Result     : Theorem 16.70s
% Output     : CNFRefutation 16.70s
% Verified   : 
% Statistics : Number of formulae       :   72 (  97 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   72 ( 116 expanded)
%              Number of equality atoms :   25 (  39 expanded)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    ! [B_92,C_93,A_94] :
      ( r2_hidden(B_92,C_93)
      | ~ r1_tarski(k2_tarski(A_94,B_92),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_311,plain,(
    ! [B_92,A_94] : r2_hidden(B_92,k2_tarski(A_94,B_92)) ),
    inference(resolution,[status(thm)],[c_12,c_298])).

tff(c_267,plain,(
    ! [A_84,C_85,B_86] :
      ( r2_hidden(A_84,C_85)
      | ~ r1_tarski(k2_tarski(A_84,B_86),C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_280,plain,(
    ! [A_84,B_86] : r2_hidden(A_84,k2_tarski(A_84,B_86)) ),
    inference(resolution,[status(thm)],[c_12,c_267])).

tff(c_163,plain,(
    ! [C_77,B_78,A_79] : k1_enumset1(C_77,B_78,A_79) = k1_enumset1(A_79,B_78,C_77) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_179,plain,(
    ! [C_77,B_78] : k1_enumset1(C_77,B_78,B_78) = k2_tarski(B_78,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_32])).

tff(c_34,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) = k3_enumset1(A_45,B_46,C_47,D_48,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1143,plain,(
    ! [B_153,D_152,A_148,F_151,E_150,C_149] : k2_xboole_0(k3_enumset1(A_148,B_153,C_149,D_152,E_150),k1_tarski(F_151)) = k4_enumset1(A_148,B_153,C_149,D_152,E_150,F_151) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7576,plain,(
    ! [E_219,C_216,D_221,A_217,B_220,F_218] : r1_tarski(k3_enumset1(A_217,B_220,C_216,D_221,E_219),k4_enumset1(A_217,B_220,C_216,D_221,E_219,F_218)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_16])).

tff(c_7584,plain,(
    ! [D_44,C_43,A_41,B_42,F_218] : r1_tarski(k2_enumset1(A_41,B_42,C_43,D_44),k4_enumset1(A_41,A_41,B_42,C_43,D_44,F_218)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7576])).

tff(c_36764,plain,(
    ! [C_368,A_367,F_370,B_371,D_369] : r1_tarski(k2_enumset1(A_367,B_371,C_368,D_369),k3_enumset1(A_367,B_371,C_368,D_369,F_370)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7584])).

tff(c_36772,plain,(
    ! [A_38,B_39,C_40,F_370] : r1_tarski(k1_enumset1(A_38,B_39,C_40),k3_enumset1(A_38,A_38,B_39,C_40,F_370)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36764])).

tff(c_36778,plain,(
    ! [A_372,B_373,C_374,F_375] : r1_tarski(k1_enumset1(A_372,B_373,C_374),k2_enumset1(A_372,B_373,C_374,F_375)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36772])).

tff(c_36783,plain,(
    ! [A_38,B_39,C_40] : r1_tarski(k1_enumset1(A_38,A_38,B_39),k1_enumset1(A_38,B_39,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36778])).

tff(c_36799,plain,(
    ! [A_376,B_377,C_378] : r1_tarski(k2_tarski(A_376,B_377),k1_enumset1(A_376,B_377,C_378)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36783])).

tff(c_37574,plain,(
    ! [C_395,B_396] : r1_tarski(k2_tarski(C_395,B_396),k2_tarski(B_396,C_395)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_36799])).

tff(c_735,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k2_tarski(A_127,B_128),C_129)
      | ~ r2_hidden(B_128,C_129)
      | ~ r2_hidden(A_127,C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_754,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_tarski(A_127,B_128) = C_129
      | ~ r1_tarski(C_129,k2_tarski(A_127,B_128))
      | ~ r2_hidden(B_128,C_129)
      | ~ r2_hidden(A_127,C_129) ) ),
    inference(resolution,[status(thm)],[c_735,c_8])).

tff(c_37577,plain,(
    ! [C_395,B_396] :
      ( k2_tarski(C_395,B_396) = k2_tarski(B_396,C_395)
      | ~ r2_hidden(C_395,k2_tarski(C_395,B_396))
      | ~ r2_hidden(B_396,k2_tarski(C_395,B_396)) ) ),
    inference(resolution,[status(thm)],[c_37574,c_754])).

tff(c_37604,plain,(
    ! [C_397,B_398] : k2_tarski(C_397,B_398) = k2_tarski(B_398,C_397) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_280,c_37577])).

tff(c_42,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37865,plain,(
    ! [B_405,C_406] : k3_tarski(k2_tarski(B_405,C_406)) = k2_xboole_0(C_406,B_405) ),
    inference(superposition,[status(thm),theory(equality)],[c_37604,c_42])).

tff(c_37871,plain,(
    ! [C_406,B_405] : k2_xboole_0(C_406,B_405) = k2_xboole_0(B_405,C_406) ),
    inference(superposition,[status(thm),theory(equality)],[c_37865,c_42])).

tff(c_52,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_247])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_37894,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37871,c_266])).

tff(c_37899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_37894])).

tff(c_37900,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_37907,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37900,c_16])).

tff(c_37937,plain,(
    ! [A_412,C_413,B_414] :
      ( r2_hidden(A_412,C_413)
      | ~ r1_tarski(k2_tarski(A_412,B_414),C_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37940,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_37907,c_37937])).

tff(c_37955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_37940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:37:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.70/10.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/10.10  
% 16.70/10.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/10.10  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 16.70/10.10  
% 16.70/10.10  %Foreground sorts:
% 16.70/10.10  
% 16.70/10.10  
% 16.70/10.10  %Background operators:
% 16.70/10.10  
% 16.70/10.10  
% 16.70/10.10  %Foreground operators:
% 16.70/10.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.70/10.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.70/10.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.70/10.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.70/10.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.70/10.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.70/10.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.70/10.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.70/10.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.70/10.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.70/10.10  tff('#skF_2', type, '#skF_2': $i).
% 16.70/10.10  tff('#skF_3', type, '#skF_3': $i).
% 16.70/10.10  tff('#skF_1', type, '#skF_1': $i).
% 16.70/10.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.70/10.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.70/10.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.70/10.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.70/10.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.70/10.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.70/10.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.70/10.10  
% 16.70/10.12  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 16.70/10.12  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.70/10.12  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.70/10.12  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 16.70/10.12  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 16.70/10.12  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 16.70/10.12  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 16.70/10.12  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 16.70/10.12  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 16.70/10.12  tff(f_51, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 16.70/10.12  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.70/10.12  tff(c_50, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.70/10.12  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.70/10.12  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.70/10.12  tff(c_298, plain, (![B_92, C_93, A_94]: (r2_hidden(B_92, C_93) | ~r1_tarski(k2_tarski(A_94, B_92), C_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.70/10.12  tff(c_311, plain, (![B_92, A_94]: (r2_hidden(B_92, k2_tarski(A_94, B_92)))), inference(resolution, [status(thm)], [c_12, c_298])).
% 16.70/10.12  tff(c_267, plain, (![A_84, C_85, B_86]: (r2_hidden(A_84, C_85) | ~r1_tarski(k2_tarski(A_84, B_86), C_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.70/10.12  tff(c_280, plain, (![A_84, B_86]: (r2_hidden(A_84, k2_tarski(A_84, B_86)))), inference(resolution, [status(thm)], [c_12, c_267])).
% 16.70/10.12  tff(c_163, plain, (![C_77, B_78, A_79]: (k1_enumset1(C_77, B_78, A_79)=k1_enumset1(A_79, B_78, C_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.70/10.12  tff(c_32, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.70/10.12  tff(c_179, plain, (![C_77, B_78]: (k1_enumset1(C_77, B_78, B_78)=k2_tarski(B_78, C_77))), inference(superposition, [status(thm), theory('equality')], [c_163, c_32])).
% 16.70/10.12  tff(c_34, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.70/10.12  tff(c_36, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.70/10.12  tff(c_38, plain, (![D_48, C_47, A_45, B_46, E_49]: (k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49)=k3_enumset1(A_45, B_46, C_47, D_48, E_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.70/10.12  tff(c_1143, plain, (![B_153, D_152, A_148, F_151, E_150, C_149]: (k2_xboole_0(k3_enumset1(A_148, B_153, C_149, D_152, E_150), k1_tarski(F_151))=k4_enumset1(A_148, B_153, C_149, D_152, E_150, F_151))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.70/10.12  tff(c_7576, plain, (![E_219, C_216, D_221, A_217, B_220, F_218]: (r1_tarski(k3_enumset1(A_217, B_220, C_216, D_221, E_219), k4_enumset1(A_217, B_220, C_216, D_221, E_219, F_218)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_16])).
% 16.70/10.12  tff(c_7584, plain, (![D_44, C_43, A_41, B_42, F_218]: (r1_tarski(k2_enumset1(A_41, B_42, C_43, D_44), k4_enumset1(A_41, A_41, B_42, C_43, D_44, F_218)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_7576])).
% 16.70/10.12  tff(c_36764, plain, (![C_368, A_367, F_370, B_371, D_369]: (r1_tarski(k2_enumset1(A_367, B_371, C_368, D_369), k3_enumset1(A_367, B_371, C_368, D_369, F_370)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7584])).
% 16.70/10.12  tff(c_36772, plain, (![A_38, B_39, C_40, F_370]: (r1_tarski(k1_enumset1(A_38, B_39, C_40), k3_enumset1(A_38, A_38, B_39, C_40, F_370)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_36764])).
% 16.70/10.12  tff(c_36778, plain, (![A_372, B_373, C_374, F_375]: (r1_tarski(k1_enumset1(A_372, B_373, C_374), k2_enumset1(A_372, B_373, C_374, F_375)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36772])).
% 16.70/10.12  tff(c_36783, plain, (![A_38, B_39, C_40]: (r1_tarski(k1_enumset1(A_38, A_38, B_39), k1_enumset1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_36778])).
% 16.70/10.12  tff(c_36799, plain, (![A_376, B_377, C_378]: (r1_tarski(k2_tarski(A_376, B_377), k1_enumset1(A_376, B_377, C_378)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36783])).
% 16.70/10.12  tff(c_37574, plain, (![C_395, B_396]: (r1_tarski(k2_tarski(C_395, B_396), k2_tarski(B_396, C_395)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_36799])).
% 16.70/10.12  tff(c_735, plain, (![A_127, B_128, C_129]: (r1_tarski(k2_tarski(A_127, B_128), C_129) | ~r2_hidden(B_128, C_129) | ~r2_hidden(A_127, C_129))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.70/10.12  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.70/10.12  tff(c_754, plain, (![A_127, B_128, C_129]: (k2_tarski(A_127, B_128)=C_129 | ~r1_tarski(C_129, k2_tarski(A_127, B_128)) | ~r2_hidden(B_128, C_129) | ~r2_hidden(A_127, C_129))), inference(resolution, [status(thm)], [c_735, c_8])).
% 16.70/10.12  tff(c_37577, plain, (![C_395, B_396]: (k2_tarski(C_395, B_396)=k2_tarski(B_396, C_395) | ~r2_hidden(C_395, k2_tarski(C_395, B_396)) | ~r2_hidden(B_396, k2_tarski(C_395, B_396)))), inference(resolution, [status(thm)], [c_37574, c_754])).
% 16.70/10.12  tff(c_37604, plain, (![C_397, B_398]: (k2_tarski(C_397, B_398)=k2_tarski(B_398, C_397))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_280, c_37577])).
% 16.70/10.12  tff(c_42, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.70/10.12  tff(c_37865, plain, (![B_405, C_406]: (k3_tarski(k2_tarski(B_405, C_406))=k2_xboole_0(C_406, B_405))), inference(superposition, [status(thm), theory('equality')], [c_37604, c_42])).
% 16.70/10.12  tff(c_37871, plain, (![C_406, B_405]: (k2_xboole_0(C_406, B_405)=k2_xboole_0(B_405, C_406))), inference(superposition, [status(thm), theory('equality')], [c_37865, c_42])).
% 16.70/10.12  tff(c_52, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.70/10.12  tff(c_247, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.70/10.12  tff(c_256, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_247])).
% 16.70/10.12  tff(c_266, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_256])).
% 16.70/10.12  tff(c_37894, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_37871, c_266])).
% 16.70/10.12  tff(c_37899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_37894])).
% 16.70/10.12  tff(c_37900, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_256])).
% 16.70/10.12  tff(c_37907, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37900, c_16])).
% 16.70/10.12  tff(c_37937, plain, (![A_412, C_413, B_414]: (r2_hidden(A_412, C_413) | ~r1_tarski(k2_tarski(A_412, B_414), C_413))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.70/10.12  tff(c_37940, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_37907, c_37937])).
% 16.70/10.12  tff(c_37955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_37940])).
% 16.70/10.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/10.12  
% 16.70/10.12  Inference rules
% 16.70/10.12  ----------------------
% 16.70/10.12  #Ref     : 0
% 16.70/10.12  #Sup     : 10070
% 16.70/10.12  #Fact    : 0
% 16.70/10.12  #Define  : 0
% 16.70/10.12  #Split   : 1
% 16.70/10.12  #Chain   : 0
% 16.70/10.12  #Close   : 0
% 16.70/10.12  
% 16.70/10.12  Ordering : KBO
% 16.70/10.12  
% 16.70/10.12  Simplification rules
% 16.70/10.12  ----------------------
% 16.70/10.12  #Subsume      : 704
% 16.70/10.12  #Demod        : 13656
% 16.70/10.12  #Tautology    : 3267
% 16.70/10.12  #SimpNegUnit  : 1
% 16.70/10.12  #BackRed      : 5
% 16.70/10.12  
% 16.70/10.12  #Partial instantiations: 0
% 16.70/10.12  #Strategies tried      : 1
% 16.70/10.12  
% 16.70/10.12  Timing (in seconds)
% 16.70/10.12  ----------------------
% 16.70/10.12  Preprocessing        : 0.33
% 16.70/10.12  Parsing              : 0.17
% 16.70/10.12  CNF conversion       : 0.02
% 16.70/10.12  Main loop            : 9.04
% 16.70/10.12  Inferencing          : 1.07
% 16.70/10.12  Reduction            : 6.63
% 16.70/10.12  Demodulation         : 6.34
% 16.70/10.12  BG Simplification    : 0.20
% 16.70/10.12  Subsumption          : 0.93
% 16.70/10.12  Abstraction          : 0.31
% 16.70/10.12  MUC search           : 0.00
% 16.70/10.12  Cooper               : 0.00
% 16.70/10.12  Total                : 9.39
% 16.70/10.12  Index Insertion      : 0.00
% 16.70/10.12  Index Deletion       : 0.00
% 16.70/10.12  Index Matching       : 0.00
% 16.70/10.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
