%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 114 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 136 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_203,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_185])).

tff(c_207,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_203])).

tff(c_810,plain,(
    ! [A_75,B_76,C_77] : k2_xboole_0(k4_xboole_0(A_75,B_76),k4_xboole_0(A_75,C_77)) = k4_xboole_0(A_75,k3_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_866,plain,(
    ! [A_16,B_76] : k4_xboole_0(A_16,k3_xboole_0(B_76,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_16,B_76),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_810])).

tff(c_919,plain,(
    ! [A_80,B_81] : k2_xboole_0(k4_xboole_0(A_80,B_81),A_80) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_866])).

tff(c_945,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_919])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_146,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_857,plain,(
    ! [C_77] : k4_xboole_0('#skF_2',k3_xboole_0('#skF_4',C_77)) = k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_810])).

tff(c_1022,plain,(
    ! [C_77] : k4_xboole_0('#skF_2',k3_xboole_0('#skF_4',C_77)) = k4_xboole_0('#skF_2',C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_857])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_132,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_132])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1543,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,k4_xboole_0(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_1617,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3'))) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_1543])).

tff(c_1646,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1617])).

tff(c_1902,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1646])).

tff(c_194,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_166,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [C_40] :
      ( ~ r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_166])).

tff(c_183,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_169])).

tff(c_381,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(A_59,k4_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_564,plain,(
    ! [A_65,B_66] : k3_xboole_0(A_65,k4_xboole_0(B_66,k3_xboole_0(A_65,B_66))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_381])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_578,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,k4_xboole_0(B_66,k3_xboole_0(A_65,B_66))),k1_xboole_0)
      | r1_xboole_0(A_65,k4_xboole_0(B_66,k3_xboole_0(A_65,B_66))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_8])).

tff(c_1271,plain,(
    ! [A_90,B_91] : r1_xboole_0(A_90,k4_xboole_0(B_91,k3_xboole_0(A_90,B_91))) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_578])).

tff(c_336,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(B_55,A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_361,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_336])).

tff(c_1366,plain,(
    ! [B_93,A_94] : r1_xboole_0(k4_xboole_0(B_93,k3_xboole_0(A_94,B_93)),A_94) ),
    inference(resolution,[status(thm)],[c_1271,c_361])).

tff(c_1402,plain,(
    ! [A_1,B_2] : r1_xboole_0(k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1366])).

tff(c_1849,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1402])).

tff(c_1906,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_1849])).

tff(c_1952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.59  
% 3.24/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.24/1.60  
% 3.24/1.60  %Foreground sorts:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Background operators:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Foreground operators:
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.60  
% 3.24/1.61  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.24/1.61  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.24/1.61  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.24/1.61  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.24/1.61  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 3.24/1.61  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.24/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.61  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.24/1.61  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.24/1.61  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.24/1.61  tff(c_32, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.61  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.61  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.24/1.61  tff(c_185, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.61  tff(c_203, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_185])).
% 3.24/1.61  tff(c_207, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_203])).
% 3.24/1.61  tff(c_810, plain, (![A_75, B_76, C_77]: (k2_xboole_0(k4_xboole_0(A_75, B_76), k4_xboole_0(A_75, C_77))=k4_xboole_0(A_75, k3_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.61  tff(c_866, plain, (![A_16, B_76]: (k4_xboole_0(A_16, k3_xboole_0(B_76, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_16, B_76), A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_810])).
% 3.24/1.61  tff(c_919, plain, (![A_80, B_81]: (k2_xboole_0(k4_xboole_0(A_80, B_81), A_80)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_866])).
% 3.24/1.61  tff(c_945, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, A_16)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_207, c_919])).
% 3.24/1.61  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.61  tff(c_142, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.61  tff(c_146, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_142])).
% 3.24/1.61  tff(c_857, plain, (![C_77]: (k4_xboole_0('#skF_2', k3_xboole_0('#skF_4', C_77))=k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', C_77)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_810])).
% 3.24/1.61  tff(c_1022, plain, (![C_77]: (k4_xboole_0('#skF_2', k3_xboole_0('#skF_4', C_77))=k4_xboole_0('#skF_2', C_77))), inference(demodulation, [status(thm), theory('equality')], [c_945, c_857])).
% 3.24/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.61  tff(c_28, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.61  tff(c_33, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 3.24/1.61  tff(c_132, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.61  tff(c_136, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_132])).
% 3.24/1.61  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.61  tff(c_1543, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k3_xboole_0(A_97, k4_xboole_0(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_185])).
% 3.24/1.61  tff(c_1617, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3')))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_1543])).
% 3.24/1.61  tff(c_1646, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1617])).
% 3.24/1.61  tff(c_1902, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1646])).
% 3.24/1.61  tff(c_194, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_185])).
% 3.24/1.61  tff(c_166, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.61  tff(c_169, plain, (![C_40]: (~r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_166])).
% 3.24/1.61  tff(c_183, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_169])).
% 3.24/1.61  tff(c_381, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.24/1.61  tff(c_564, plain, (![A_65, B_66]: (k3_xboole_0(A_65, k4_xboole_0(B_66, k3_xboole_0(A_65, B_66)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_207, c_381])).
% 3.24/1.61  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.61  tff(c_578, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, k4_xboole_0(B_66, k3_xboole_0(A_65, B_66))), k1_xboole_0) | r1_xboole_0(A_65, k4_xboole_0(B_66, k3_xboole_0(A_65, B_66))))), inference(superposition, [status(thm), theory('equality')], [c_564, c_8])).
% 3.24/1.61  tff(c_1271, plain, (![A_90, B_91]: (r1_xboole_0(A_90, k4_xboole_0(B_91, k3_xboole_0(A_90, B_91))))), inference(negUnitSimplification, [status(thm)], [c_183, c_578])).
% 3.24/1.61  tff(c_336, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(B_55, A_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_166])).
% 3.24/1.61  tff(c_361, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_336])).
% 3.24/1.61  tff(c_1366, plain, (![B_93, A_94]: (r1_xboole_0(k4_xboole_0(B_93, k3_xboole_0(A_94, B_93)), A_94))), inference(resolution, [status(thm)], [c_1271, c_361])).
% 3.24/1.61  tff(c_1402, plain, (![A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_1, k3_xboole_0(A_1, B_2)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1366])).
% 3.24/1.61  tff(c_1849, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_1402])).
% 3.24/1.61  tff(c_1906, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1902, c_1849])).
% 3.24/1.61  tff(c_1952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1906])).
% 3.24/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  
% 3.24/1.61  Inference rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Ref     : 0
% 3.24/1.61  #Sup     : 483
% 3.24/1.61  #Fact    : 0
% 3.24/1.61  #Define  : 0
% 3.24/1.61  #Split   : 2
% 3.24/1.61  #Chain   : 0
% 3.24/1.61  #Close   : 0
% 3.24/1.61  
% 3.24/1.61  Ordering : KBO
% 3.24/1.61  
% 3.24/1.61  Simplification rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Subsume      : 26
% 3.24/1.61  #Demod        : 356
% 3.24/1.61  #Tautology    : 293
% 3.24/1.61  #SimpNegUnit  : 8
% 3.24/1.61  #BackRed      : 3
% 3.24/1.61  
% 3.24/1.61  #Partial instantiations: 0
% 3.24/1.61  #Strategies tried      : 1
% 3.24/1.61  
% 3.24/1.61  Timing (in seconds)
% 3.24/1.61  ----------------------
% 3.24/1.61  Preprocessing        : 0.30
% 3.24/1.61  Parsing              : 0.16
% 3.24/1.61  CNF conversion       : 0.02
% 3.24/1.61  Main loop            : 0.49
% 3.24/1.61  Inferencing          : 0.16
% 3.24/1.61  Reduction            : 0.20
% 3.24/1.61  Demodulation         : 0.16
% 3.24/1.61  BG Simplification    : 0.02
% 3.24/1.61  Subsumption          : 0.08
% 3.24/1.61  Abstraction          : 0.02
% 3.24/1.61  MUC search           : 0.00
% 3.24/1.61  Cooper               : 0.00
% 3.24/1.61  Total                : 0.82
% 3.24/1.62  Index Insertion      : 0.00
% 3.24/1.62  Index Deletion       : 0.00
% 3.24/1.62  Index Matching       : 0.00
% 3.24/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
