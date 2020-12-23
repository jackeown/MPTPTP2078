%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 382 expanded)
%              Number of leaves         :   28 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 544 expanded)
%              Number of equality atoms :   52 ( 297 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [A_48,B_49] :
      ( ~ r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_210,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_195])).

tff(c_301,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_322,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_301])).

tff(c_332,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_322])).

tff(c_36,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_37,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_84,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_28])).

tff(c_144,plain,(
    r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_135])).

tff(c_507,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k4_xboole_0(A_61,B_62),C_63)
      | ~ r1_tarski(A_61,k2_xboole_0(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7893,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_xboole_0(k4_xboole_0(A_149,B_150),C_151) = C_151
      | ~ r1_tarski(A_149,k2_xboole_0(B_150,C_151)) ) ),
    inference(resolution,[status(thm)],[c_507,c_14])).

tff(c_8048,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_144,c_7893])).

tff(c_8131,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_332,c_8048])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_208,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_195])).

tff(c_325,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_301])).

tff(c_333,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_325])).

tff(c_64,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_28])).

tff(c_151,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_151])).

tff(c_123,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_84])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_793,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k2_xboole_0(A_66,B_67),C_68) = k2_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_861,plain,(
    ! [C_68] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_68) = k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_793])).

tff(c_1066,plain,(
    ! [C_71] : k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_71)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_861])).

tff(c_1097,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1066])).

tff(c_1115,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1097])).

tff(c_105,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_28])).

tff(c_5280,plain,(
    r1_tarski(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_105])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11438,plain,(
    ! [A_183,B_184,C_185] :
      ( r1_tarski(k4_xboole_0(A_183,B_184),C_185)
      | ~ r1_tarski(k2_xboole_0(A_183,B_184),k2_xboole_0(B_184,C_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_507])).

tff(c_11723,plain,(
    ! [A_186] :
      ( r1_tarski(k4_xboole_0(A_186,'#skF_5'),'#skF_6')
      | ~ r1_tarski(k2_xboole_0(A_186,'#skF_5'),k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_11438])).

tff(c_11738,plain,(
    r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5280,c_11723])).

tff(c_11775,plain,(
    r1_tarski('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_11738])).

tff(c_11785,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11775,c_14])).

tff(c_11787,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8131,c_11785])).

tff(c_73,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_209,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_195])).

tff(c_316,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_301])).

tff(c_330,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_316])).

tff(c_11828,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_330])).

tff(c_211,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_319,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_301])).

tff(c_331,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_319])).

tff(c_342,plain,(
    ! [A_56,B_57] : k4_xboole_0(k2_xboole_0(A_56,B_57),B_57) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_367,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_342])).

tff(c_11827,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_11787,c_367])).

tff(c_11861,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_18,c_11827])).

tff(c_12122,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11828,c_11861])).

tff(c_12124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_12122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.76/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.88  
% 7.76/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.76/2.88  
% 7.76/2.88  %Foreground sorts:
% 7.76/2.88  
% 7.76/2.88  
% 7.76/2.88  %Background operators:
% 7.76/2.88  
% 7.76/2.88  
% 7.76/2.88  %Foreground operators:
% 7.76/2.88  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.76/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.76/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.76/2.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.76/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.76/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.76/2.88  tff('#skF_5', type, '#skF_5': $i).
% 7.76/2.88  tff('#skF_6', type, '#skF_6': $i).
% 7.76/2.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.76/2.88  tff('#skF_3', type, '#skF_3': $i).
% 7.76/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.76/2.88  tff('#skF_4', type, '#skF_4': $i).
% 7.76/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.76/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.76/2.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.76/2.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.76/2.88  
% 7.76/2.89  tff(f_84, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 7.76/2.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.76/2.89  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.76/2.89  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.76/2.89  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.76/2.89  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.76/2.89  tff(f_75, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.76/2.89  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.76/2.89  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.76/2.89  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.76/2.89  tff(f_73, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.76/2.89  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.76/2.89  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.76/2.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.76/2.89  tff(c_16, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.76/2.89  tff(c_32, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.76/2.89  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.76/2.89  tff(c_189, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.76/2.89  tff(c_195, plain, (![A_48, B_49]: (~r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_189])).
% 7.76/2.89  tff(c_210, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_195])).
% 7.76/2.89  tff(c_301, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.76/2.89  tff(c_322, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_210, c_301])).
% 7.76/2.89  tff(c_332, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_322])).
% 7.76/2.89  tff(c_36, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.76/2.89  tff(c_37, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 7.76/2.89  tff(c_84, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.76/2.89  tff(c_28, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.76/2.89  tff(c_135, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_28])).
% 7.76/2.89  tff(c_144, plain, (r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_135])).
% 7.76/2.89  tff(c_507, plain, (![A_61, B_62, C_63]: (r1_tarski(k4_xboole_0(A_61, B_62), C_63) | ~r1_tarski(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.76/2.89  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.76/2.89  tff(c_7893, plain, (![A_149, B_150, C_151]: (k2_xboole_0(k4_xboole_0(A_149, B_150), C_151)=C_151 | ~r1_tarski(A_149, k2_xboole_0(B_150, C_151)))), inference(resolution, [status(thm)], [c_507, c_14])).
% 7.76/2.89  tff(c_8048, plain, (k2_xboole_0(k4_xboole_0('#skF_6', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_144, c_7893])).
% 7.76/2.89  tff(c_8131, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_332, c_8048])).
% 7.76/2.89  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.76/2.89  tff(c_68, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.76/2.89  tff(c_74, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_68])).
% 7.76/2.89  tff(c_208, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_195])).
% 7.76/2.89  tff(c_325, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_208, c_301])).
% 7.76/2.89  tff(c_333, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_325])).
% 7.76/2.89  tff(c_64, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_28])).
% 7.76/2.89  tff(c_151, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.76/2.89  tff(c_165, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_151])).
% 7.76/2.89  tff(c_123, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37, c_84])).
% 7.76/2.89  tff(c_26, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.76/2.89  tff(c_793, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k2_xboole_0(A_66, B_67), C_68)=k2_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.76/2.89  tff(c_861, plain, (![C_68]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_68)=k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_68)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_793])).
% 7.76/2.89  tff(c_1066, plain, (![C_71]: (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_71))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_71)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_861])).
% 7.76/2.89  tff(c_1097, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1066])).
% 7.76/2.89  tff(c_1115, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1097])).
% 7.76/2.89  tff(c_105, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_28])).
% 7.76/2.89  tff(c_5280, plain, (r1_tarski(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1115, c_105])).
% 7.76/2.89  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.76/2.89  tff(c_11438, plain, (![A_183, B_184, C_185]: (r1_tarski(k4_xboole_0(A_183, B_184), C_185) | ~r1_tarski(k2_xboole_0(A_183, B_184), k2_xboole_0(B_184, C_185)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_507])).
% 7.76/2.89  tff(c_11723, plain, (![A_186]: (r1_tarski(k4_xboole_0(A_186, '#skF_5'), '#skF_6') | ~r1_tarski(k2_xboole_0(A_186, '#skF_5'), k2_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_37, c_11438])).
% 7.76/2.89  tff(c_11738, plain, (r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_5280, c_11723])).
% 7.76/2.89  tff(c_11775, plain, (r1_tarski('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_11738])).
% 7.76/2.89  tff(c_11785, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_11775, c_14])).
% 7.76/2.89  tff(c_11787, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8131, c_11785])).
% 7.76/2.89  tff(c_73, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_68])).
% 7.76/2.89  tff(c_209, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_195])).
% 7.76/2.89  tff(c_316, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_209, c_301])).
% 7.76/2.89  tff(c_330, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_316])).
% 7.76/2.89  tff(c_11828, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_330])).
% 7.76/2.89  tff(c_211, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_195])).
% 7.76/2.89  tff(c_319, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_211, c_301])).
% 7.76/2.89  tff(c_331, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_319])).
% 7.76/2.89  tff(c_342, plain, (![A_56, B_57]: (k4_xboole_0(k2_xboole_0(A_56, B_57), B_57)=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.76/2.89  tff(c_367, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_37, c_342])).
% 7.76/2.89  tff(c_11827, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_11787, c_367])).
% 7.76/2.89  tff(c_11861, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_18, c_11827])).
% 7.76/2.89  tff(c_12122, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11828, c_11861])).
% 7.76/2.89  tff(c_12124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_12122])).
% 7.76/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.89  
% 7.76/2.89  Inference rules
% 7.76/2.89  ----------------------
% 7.76/2.89  #Ref     : 0
% 7.76/2.89  #Sup     : 3003
% 7.76/2.89  #Fact    : 0
% 7.76/2.89  #Define  : 0
% 7.76/2.89  #Split   : 2
% 7.76/2.89  #Chain   : 0
% 7.76/2.89  #Close   : 0
% 7.76/2.89  
% 7.76/2.89  Ordering : KBO
% 7.76/2.89  
% 7.76/2.89  Simplification rules
% 7.76/2.89  ----------------------
% 7.76/2.89  #Subsume      : 77
% 7.76/2.89  #Demod        : 3132
% 7.76/2.89  #Tautology    : 1775
% 7.76/2.89  #SimpNegUnit  : 18
% 7.76/2.89  #BackRed      : 54
% 7.76/2.89  
% 7.76/2.89  #Partial instantiations: 0
% 7.76/2.89  #Strategies tried      : 1
% 7.76/2.89  
% 7.76/2.89  Timing (in seconds)
% 7.76/2.89  ----------------------
% 7.76/2.90  Preprocessing        : 0.28
% 7.76/2.90  Parsing              : 0.15
% 7.76/2.90  CNF conversion       : 0.02
% 7.76/2.90  Main loop            : 1.79
% 7.76/2.90  Inferencing          : 0.42
% 7.76/2.90  Reduction            : 0.95
% 7.76/2.90  Demodulation         : 0.83
% 7.76/2.90  BG Simplification    : 0.05
% 7.76/2.90  Subsumption          : 0.28
% 7.76/2.90  Abstraction          : 0.06
% 7.76/2.90  MUC search           : 0.00
% 7.76/2.90  Cooper               : 0.00
% 7.76/2.90  Total                : 2.11
% 7.76/2.90  Index Insertion      : 0.00
% 7.76/2.90  Index Deletion       : 0.00
% 7.76/2.90  Index Matching       : 0.00
% 7.76/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
