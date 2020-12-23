%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:07 EST 2020

% Result     : Theorem 13.32s
% Output     : CNFRefutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 231 expanded)
%              Number of leaves         :   32 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 ( 264 expanded)
%              Number of equality atoms :   28 ( 122 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_56,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_45,B_46,C_47,D_48] : k3_enumset1(A_45,A_45,B_46,C_47,D_48) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [D_52,C_51,B_50,A_49,E_53] : k4_enumset1(A_49,A_49,B_50,C_51,D_52,E_53) = k3_enumset1(A_49,B_50,C_51,D_52,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1596,plain,(
    ! [D_170,F_173,B_174,A_171,E_175,C_172] : k2_xboole_0(k3_enumset1(A_171,B_174,C_172,D_170,E_175),k1_tarski(F_173)) = k4_enumset1(A_171,B_174,C_172,D_170,E_175,F_173) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5395,plain,(
    ! [D_234,C_231,E_233,A_232,F_229,B_230] : r1_tarski(k3_enumset1(A_232,B_230,C_231,D_234,E_233),k4_enumset1(A_232,B_230,C_231,D_234,E_233,F_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_22])).

tff(c_5403,plain,(
    ! [D_48,C_47,A_45,B_46,F_229] : r1_tarski(k2_enumset1(A_45,B_46,C_47,D_48),k4_enumset1(A_45,A_45,B_46,C_47,D_48,F_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5395])).

tff(c_24979,plain,(
    ! [D_368,A_367,F_370,B_366,C_369] : r1_tarski(k2_enumset1(A_367,B_366,C_369,D_368),k3_enumset1(A_367,B_366,C_369,D_368,F_370)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5403])).

tff(c_24984,plain,(
    ! [A_45,B_46,C_47,D_48] : r1_tarski(k2_enumset1(A_45,A_45,B_46,C_47),k2_enumset1(A_45,B_46,C_47,D_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_24979])).

tff(c_25000,plain,(
    ! [A_371,B_372,C_373,D_374] : r1_tarski(k1_enumset1(A_371,B_372,C_373),k2_enumset1(A_371,B_372,C_373,D_374)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24984])).

tff(c_25020,plain,(
    ! [A_42,B_43,C_44] : r1_tarski(k1_enumset1(A_42,A_42,B_43),k1_enumset1(A_42,B_43,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_25000])).

tff(c_25027,plain,(
    ! [A_375,B_376,C_377] : r1_tarski(k2_tarski(A_375,B_376),k1_enumset1(A_375,B_376,C_377)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_25020])).

tff(c_52,plain,(
    ! [B_70,C_71,A_69] :
      ( r2_hidden(B_70,C_71)
      | ~ r1_tarski(k2_tarski(A_69,B_70),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_25048,plain,(
    ! [B_376,A_375,C_377] : r2_hidden(B_376,k1_enumset1(A_375,B_376,C_377)) ),
    inference(resolution,[status(thm)],[c_25027,c_52])).

tff(c_54,plain,(
    ! [A_69,C_71,B_70] :
      ( r2_hidden(A_69,C_71)
      | ~ r1_tarski(k2_tarski(A_69,B_70),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_25049,plain,(
    ! [A_375,B_376,C_377] : r2_hidden(A_375,k1_enumset1(A_375,B_376,C_377)) ),
    inference(resolution,[status(thm)],[c_25027,c_54])).

tff(c_523,plain,(
    ! [D_127,C_128,B_129,A_130] : k2_enumset1(D_127,C_128,B_129,A_130) = k2_enumset1(A_130,B_129,C_128,D_127) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_539,plain,(
    ! [D_127,C_128,B_129] : k2_enumset1(D_127,C_128,B_129,B_129) = k1_enumset1(B_129,C_128,D_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_38])).

tff(c_25133,plain,(
    ! [D_388,C_389,B_390] : r1_tarski(k1_enumset1(D_388,C_389,B_390),k1_enumset1(B_390,C_389,D_388)) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_25000])).

tff(c_25162,plain,(
    ! [B_391,A_392] : r1_tarski(k1_enumset1(B_391,A_392,A_392),k2_tarski(A_392,B_391)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_25133])).

tff(c_997,plain,(
    ! [A_149,B_150,C_151] :
      ( r1_tarski(k2_tarski(A_149,B_150),C_151)
      | ~ r2_hidden(B_150,C_151)
      | ~ r2_hidden(A_149,C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1021,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_tarski(A_149,B_150) = C_151
      | ~ r1_tarski(C_151,k2_tarski(A_149,B_150))
      | ~ r2_hidden(B_150,C_151)
      | ~ r2_hidden(A_149,C_151) ) ),
    inference(resolution,[status(thm)],[c_997,c_8])).

tff(c_25165,plain,(
    ! [B_391,A_392] :
      ( k1_enumset1(B_391,A_392,A_392) = k2_tarski(A_392,B_391)
      | ~ r2_hidden(B_391,k1_enumset1(B_391,A_392,A_392))
      | ~ r2_hidden(A_392,k1_enumset1(B_391,A_392,A_392)) ) ),
    inference(resolution,[status(thm)],[c_25162,c_1021])).

tff(c_25183,plain,(
    ! [B_391,A_392] : k1_enumset1(B_391,A_392,A_392) = k2_tarski(A_392,B_391) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25048,c_25049,c_25165])).

tff(c_570,plain,(
    ! [D_131,C_132,B_133] : k2_enumset1(D_131,C_132,B_133,B_133) = k1_enumset1(B_133,C_132,D_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_38])).

tff(c_583,plain,(
    ! [C_132,B_133] : k1_enumset1(C_132,B_133,B_133) = k1_enumset1(B_133,C_132,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_38])).

tff(c_25235,plain,(
    ! [C_395,B_396] : k2_tarski(C_395,B_396) = k2_tarski(B_396,C_395) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25183,c_25183,c_583])).

tff(c_48,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25436,plain,(
    ! [B_401,C_402] : k3_tarski(k2_tarski(B_401,C_402)) = k2_xboole_0(C_402,B_401) ),
    inference(superposition,[status(thm),theory(equality)],[c_25235,c_48])).

tff(c_25442,plain,(
    ! [C_402,B_401] : k2_xboole_0(C_402,B_401) = k2_xboole_0(B_401,C_402) ),
    inference(superposition,[status(thm),theory(equality)],[c_25436,c_48])).

tff(c_58,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_269,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_269])).

tff(c_385,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_25465,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25442,c_385])).

tff(c_25469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_25465])).

tff(c_25470,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_25477,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25470,c_22])).

tff(c_25486,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_25477,c_54])).

tff(c_25493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_25486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.32/6.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.88  
% 13.32/6.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.88  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.32/6.88  
% 13.32/6.88  %Foreground sorts:
% 13.32/6.88  
% 13.32/6.88  
% 13.32/6.88  %Background operators:
% 13.32/6.88  
% 13.32/6.88  
% 13.32/6.88  %Foreground operators:
% 13.32/6.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.32/6.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.32/6.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.32/6.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.32/6.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.32/6.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.32/6.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.32/6.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.32/6.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.32/6.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.32/6.88  tff('#skF_2', type, '#skF_2': $i).
% 13.32/6.88  tff('#skF_3', type, '#skF_3': $i).
% 13.32/6.88  tff('#skF_1', type, '#skF_1': $i).
% 13.32/6.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.32/6.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.32/6.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.32/6.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.32/6.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.32/6.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.88  
% 13.32/6.90  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 13.32/6.90  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.32/6.90  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.32/6.90  tff(f_63, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 13.32/6.90  tff(f_65, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 13.32/6.90  tff(f_67, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 13.32/6.90  tff(f_55, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 13.32/6.90  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 13.32/6.90  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 13.32/6.90  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.32/6.90  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.32/6.90  tff(c_56, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.32/6.90  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.32/6.90  tff(c_36, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.32/6.90  tff(c_38, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.32/6.90  tff(c_40, plain, (![A_45, B_46, C_47, D_48]: (k3_enumset1(A_45, A_45, B_46, C_47, D_48)=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.32/6.90  tff(c_42, plain, (![D_52, C_51, B_50, A_49, E_53]: (k4_enumset1(A_49, A_49, B_50, C_51, D_52, E_53)=k3_enumset1(A_49, B_50, C_51, D_52, E_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.32/6.90  tff(c_1596, plain, (![D_170, F_173, B_174, A_171, E_175, C_172]: (k2_xboole_0(k3_enumset1(A_171, B_174, C_172, D_170, E_175), k1_tarski(F_173))=k4_enumset1(A_171, B_174, C_172, D_170, E_175, F_173))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.32/6.90  tff(c_5395, plain, (![D_234, C_231, E_233, A_232, F_229, B_230]: (r1_tarski(k3_enumset1(A_232, B_230, C_231, D_234, E_233), k4_enumset1(A_232, B_230, C_231, D_234, E_233, F_229)))), inference(superposition, [status(thm), theory('equality')], [c_1596, c_22])).
% 13.32/6.90  tff(c_5403, plain, (![D_48, C_47, A_45, B_46, F_229]: (r1_tarski(k2_enumset1(A_45, B_46, C_47, D_48), k4_enumset1(A_45, A_45, B_46, C_47, D_48, F_229)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5395])).
% 13.32/6.90  tff(c_24979, plain, (![D_368, A_367, F_370, B_366, C_369]: (r1_tarski(k2_enumset1(A_367, B_366, C_369, D_368), k3_enumset1(A_367, B_366, C_369, D_368, F_370)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5403])).
% 13.32/6.90  tff(c_24984, plain, (![A_45, B_46, C_47, D_48]: (r1_tarski(k2_enumset1(A_45, A_45, B_46, C_47), k2_enumset1(A_45, B_46, C_47, D_48)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_24979])).
% 13.32/6.90  tff(c_25000, plain, (![A_371, B_372, C_373, D_374]: (r1_tarski(k1_enumset1(A_371, B_372, C_373), k2_enumset1(A_371, B_372, C_373, D_374)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24984])).
% 13.32/6.90  tff(c_25020, plain, (![A_42, B_43, C_44]: (r1_tarski(k1_enumset1(A_42, A_42, B_43), k1_enumset1(A_42, B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_25000])).
% 13.32/6.90  tff(c_25027, plain, (![A_375, B_376, C_377]: (r1_tarski(k2_tarski(A_375, B_376), k1_enumset1(A_375, B_376, C_377)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_25020])).
% 13.32/6.90  tff(c_52, plain, (![B_70, C_71, A_69]: (r2_hidden(B_70, C_71) | ~r1_tarski(k2_tarski(A_69, B_70), C_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.32/6.90  tff(c_25048, plain, (![B_376, A_375, C_377]: (r2_hidden(B_376, k1_enumset1(A_375, B_376, C_377)))), inference(resolution, [status(thm)], [c_25027, c_52])).
% 13.32/6.90  tff(c_54, plain, (![A_69, C_71, B_70]: (r2_hidden(A_69, C_71) | ~r1_tarski(k2_tarski(A_69, B_70), C_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.32/6.90  tff(c_25049, plain, (![A_375, B_376, C_377]: (r2_hidden(A_375, k1_enumset1(A_375, B_376, C_377)))), inference(resolution, [status(thm)], [c_25027, c_54])).
% 13.32/6.90  tff(c_523, plain, (![D_127, C_128, B_129, A_130]: (k2_enumset1(D_127, C_128, B_129, A_130)=k2_enumset1(A_130, B_129, C_128, D_127))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.32/6.90  tff(c_539, plain, (![D_127, C_128, B_129]: (k2_enumset1(D_127, C_128, B_129, B_129)=k1_enumset1(B_129, C_128, D_127))), inference(superposition, [status(thm), theory('equality')], [c_523, c_38])).
% 13.32/6.90  tff(c_25133, plain, (![D_388, C_389, B_390]: (r1_tarski(k1_enumset1(D_388, C_389, B_390), k1_enumset1(B_390, C_389, D_388)))), inference(superposition, [status(thm), theory('equality')], [c_539, c_25000])).
% 13.32/6.90  tff(c_25162, plain, (![B_391, A_392]: (r1_tarski(k1_enumset1(B_391, A_392, A_392), k2_tarski(A_392, B_391)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_25133])).
% 13.32/6.90  tff(c_997, plain, (![A_149, B_150, C_151]: (r1_tarski(k2_tarski(A_149, B_150), C_151) | ~r2_hidden(B_150, C_151) | ~r2_hidden(A_149, C_151))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.32/6.90  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/6.90  tff(c_1021, plain, (![A_149, B_150, C_151]: (k2_tarski(A_149, B_150)=C_151 | ~r1_tarski(C_151, k2_tarski(A_149, B_150)) | ~r2_hidden(B_150, C_151) | ~r2_hidden(A_149, C_151))), inference(resolution, [status(thm)], [c_997, c_8])).
% 13.32/6.90  tff(c_25165, plain, (![B_391, A_392]: (k1_enumset1(B_391, A_392, A_392)=k2_tarski(A_392, B_391) | ~r2_hidden(B_391, k1_enumset1(B_391, A_392, A_392)) | ~r2_hidden(A_392, k1_enumset1(B_391, A_392, A_392)))), inference(resolution, [status(thm)], [c_25162, c_1021])).
% 13.32/6.90  tff(c_25183, plain, (![B_391, A_392]: (k1_enumset1(B_391, A_392, A_392)=k2_tarski(A_392, B_391))), inference(demodulation, [status(thm), theory('equality')], [c_25048, c_25049, c_25165])).
% 13.32/6.90  tff(c_570, plain, (![D_131, C_132, B_133]: (k2_enumset1(D_131, C_132, B_133, B_133)=k1_enumset1(B_133, C_132, D_131))), inference(superposition, [status(thm), theory('equality')], [c_523, c_38])).
% 13.32/6.90  tff(c_583, plain, (![C_132, B_133]: (k1_enumset1(C_132, B_133, B_133)=k1_enumset1(B_133, C_132, C_132))), inference(superposition, [status(thm), theory('equality')], [c_570, c_38])).
% 13.32/6.90  tff(c_25235, plain, (![C_395, B_396]: (k2_tarski(C_395, B_396)=k2_tarski(B_396, C_395))), inference(demodulation, [status(thm), theory('equality')], [c_25183, c_25183, c_583])).
% 13.32/6.90  tff(c_48, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.32/6.90  tff(c_25436, plain, (![B_401, C_402]: (k3_tarski(k2_tarski(B_401, C_402))=k2_xboole_0(C_402, B_401))), inference(superposition, [status(thm), theory('equality')], [c_25235, c_48])).
% 13.32/6.90  tff(c_25442, plain, (![C_402, B_401]: (k2_xboole_0(C_402, B_401)=k2_xboole_0(B_401, C_402))), inference(superposition, [status(thm), theory('equality')], [c_25436, c_48])).
% 13.32/6.90  tff(c_58, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.32/6.90  tff(c_269, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/6.90  tff(c_282, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_269])).
% 13.32/6.90  tff(c_385, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_282])).
% 13.32/6.90  tff(c_25465, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25442, c_385])).
% 13.32/6.90  tff(c_25469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_25465])).
% 13.32/6.90  tff(c_25470, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_282])).
% 13.32/6.90  tff(c_25477, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25470, c_22])).
% 13.32/6.90  tff(c_25486, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_25477, c_54])).
% 13.32/6.90  tff(c_25493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_25486])).
% 13.32/6.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.90  
% 13.32/6.90  Inference rules
% 13.32/6.90  ----------------------
% 13.32/6.90  #Ref     : 0
% 13.32/6.90  #Sup     : 6674
% 13.32/6.90  #Fact    : 0
% 13.32/6.90  #Define  : 0
% 13.32/6.90  #Split   : 1
% 13.32/6.90  #Chain   : 0
% 13.32/6.90  #Close   : 0
% 13.32/6.90  
% 13.32/6.90  Ordering : KBO
% 13.32/6.90  
% 13.32/6.90  Simplification rules
% 13.32/6.90  ----------------------
% 13.32/6.90  #Subsume      : 534
% 13.32/6.90  #Demod        : 9946
% 13.32/6.90  #Tautology    : 2371
% 13.32/6.90  #SimpNegUnit  : 1
% 13.32/6.90  #BackRed      : 9
% 13.32/6.90  
% 13.32/6.90  #Partial instantiations: 0
% 13.32/6.90  #Strategies tried      : 1
% 13.32/6.90  
% 13.32/6.90  Timing (in seconds)
% 13.32/6.90  ----------------------
% 13.32/6.90  Preprocessing        : 0.34
% 13.32/6.90  Parsing              : 0.18
% 13.32/6.90  CNF conversion       : 0.02
% 13.32/6.90  Main loop            : 5.80
% 13.32/6.90  Inferencing          : 0.76
% 13.32/6.90  Reduction            : 4.20
% 13.32/6.90  Demodulation         : 3.99
% 13.32/6.90  BG Simplification    : 0.15
% 13.32/6.90  Subsumption          : 0.55
% 13.32/6.90  Abstraction          : 0.22
% 13.32/6.90  MUC search           : 0.00
% 13.32/6.90  Cooper               : 0.00
% 13.32/6.90  Total                : 6.17
% 13.32/6.90  Index Insertion      : 0.00
% 13.32/6.90  Index Deletion       : 0.00
% 13.32/6.90  Index Matching       : 0.00
% 13.32/6.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
