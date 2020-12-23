%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 12.62s
% Output     : CNFRefutation 12.62s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 161 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 173 expanded)
%              Number of equality atoms :   55 ( 122 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_194,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_109,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_198,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_247,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_228])).

tff(c_24,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_199,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_199])).

tff(c_515,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k3_xboole_0(A_69,B_70),C_71) = k3_xboole_0(A_69,k4_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1574,plain,(
    ! [A_93,B_94,C_95] : r1_xboole_0(k3_xboole_0(A_93,k4_xboole_0(B_94,C_95)),C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_26])).

tff(c_1611,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1574])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_288,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_302,plain,(
    ! [A_52,B_53] :
      ( ~ r1_xboole_0(A_52,B_53)
      | k3_xboole_0(A_52,B_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_288])).

tff(c_1624,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1611,c_302])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1688,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_16])).

tff(c_1696,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1688])).

tff(c_6770,plain,(
    ! [A_171,B_172,C_173] : k4_xboole_0(k3_xboole_0(A_171,B_172),C_173) = k3_xboole_0(B_172,k4_xboole_0(A_171,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_515])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k4_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_33184,plain,(
    ! [B_419,A_420,C_421] : k3_xboole_0(B_419,k4_xboole_0(A_420,C_421)) = k3_xboole_0(A_420,k4_xboole_0(B_419,C_421)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6770,c_22])).

tff(c_33999,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_33184,c_207])).

tff(c_34363,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1696,c_33999])).

tff(c_62,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_30,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1053,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1117,plain,(
    ! [A_30,C_83] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1053])).

tff(c_1131,plain,(
    ! [A_84,C_85] : k5_xboole_0(A_84,k5_xboole_0(A_84,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1117])).

tff(c_1164,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1131])).

tff(c_1733,plain,(
    ! [B_98,A_99] : k5_xboole_0(B_98,k3_xboole_0(A_99,B_98)) = k4_xboole_0(B_98,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_228])).

tff(c_1130,plain,(
    ! [A_30,C_83] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1117])).

tff(c_14339,plain,(
    ! [B_288,A_289] : k5_xboole_0(B_288,k4_xboole_0(B_288,A_289)) = k3_xboole_0(A_289,B_288) ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_1130])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4120,plain,(
    ! [A_140,A_138,B_139] : k5_xboole_0(A_140,k5_xboole_0(A_138,B_139)) = k5_xboole_0(A_138,k5_xboole_0(B_139,A_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1053])).

tff(c_4353,plain,(
    ! [A_36,A_140] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_36,A_140)) = k5_xboole_0(A_140,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4120])).

tff(c_14348,plain,(
    ! [B_288,A_289] : k5_xboole_0(k4_xboole_0(B_288,A_289),B_288) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_289,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14339,c_4353])).

tff(c_17002,plain,(
    ! [B_317,A_318] : k5_xboole_0(k4_xboole_0(B_317,A_318),B_317) = k3_xboole_0(A_318,B_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14348])).

tff(c_12469,plain,(
    ! [A_262,A_263] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_262,A_263)) = k5_xboole_0(A_263,A_262) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4120])).

tff(c_1174,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1131])).

tff(c_12510,plain,(
    ! [A_262,A_263] : k5_xboole_0(k5_xboole_0(A_262,A_263),k5_xboole_0(A_263,A_262)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12469,c_1174])).

tff(c_17008,plain,(
    ! [A_318,B_317] : k5_xboole_0(k3_xboole_0(A_318,B_317),k5_xboole_0(B_317,k4_xboole_0(B_317,A_318))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17002,c_12510])).

tff(c_17135,plain,(
    ! [A_318,B_317] : k5_xboole_0(k3_xboole_0(A_318,B_317),k3_xboole_0(B_317,A_318)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_17008])).

tff(c_34412,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34363,c_17135])).

tff(c_34571,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_2,c_34412])).

tff(c_34573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_34571])).

tff(c_34574,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34688,plain,(
    ! [A_430,B_431] :
      ( k3_xboole_0(A_430,B_431) = A_430
      | ~ r1_tarski(A_430,B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34700,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_34688])).

tff(c_34881,plain,(
    ! [A_443,B_444,C_445] : k4_xboole_0(k3_xboole_0(A_443,B_444),C_445) = k3_xboole_0(A_443,k4_xboole_0(B_444,C_445)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35843,plain,(
    ! [A_470,B_471,C_472] : r1_xboole_0(k3_xboole_0(A_470,k4_xboole_0(B_471,C_472)),C_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_34881,c_26])).

tff(c_35880,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34700,c_35843])).

tff(c_35898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34574,c_35880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.62/5.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.62/5.93  
% 12.62/5.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.62/5.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 12.62/5.93  
% 12.62/5.93  %Foreground sorts:
% 12.62/5.93  
% 12.62/5.93  
% 12.62/5.93  %Background operators:
% 12.62/5.93  
% 12.62/5.93  
% 12.62/5.93  %Foreground operators:
% 12.62/5.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.62/5.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.62/5.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.62/5.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.62/5.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.62/5.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.62/5.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.62/5.93  tff('#skF_5', type, '#skF_5': $i).
% 12.62/5.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.62/5.93  tff('#skF_3', type, '#skF_3': $i).
% 12.62/5.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.62/5.93  tff('#skF_4', type, '#skF_4': $i).
% 12.62/5.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.62/5.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.62/5.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.62/5.93  
% 12.62/5.95  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.62/5.95  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.62/5.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.62/5.95  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.62/5.95  tff(f_67, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.62/5.95  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.62/5.95  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.62/5.95  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 12.62/5.95  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 12.62/5.95  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.62/5.95  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.62/5.95  tff(f_73, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.62/5.95  tff(f_71, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.62/5.95  tff(c_194, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.62/5.95  tff(c_32, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.62/5.95  tff(c_109, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 12.62/5.95  tff(c_198, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_109])).
% 12.62/5.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.62/5.95  tff(c_228, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.62/5.95  tff(c_247, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_228])).
% 12.62/5.95  tff(c_24, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.62/5.95  tff(c_34, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.62/5.95  tff(c_199, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.62/5.95  tff(c_207, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_199])).
% 12.62/5.95  tff(c_515, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k3_xboole_0(A_69, B_70), C_71)=k3_xboole_0(A_69, k4_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.62/5.95  tff(c_26, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.62/5.95  tff(c_1574, plain, (![A_93, B_94, C_95]: (r1_xboole_0(k3_xboole_0(A_93, k4_xboole_0(B_94, C_95)), C_95))), inference(superposition, [status(thm), theory('equality')], [c_515, c_26])).
% 12.62/5.95  tff(c_1611, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_207, c_1574])).
% 12.62/5.95  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.62/5.95  tff(c_288, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.62/5.95  tff(c_302, plain, (![A_52, B_53]: (~r1_xboole_0(A_52, B_53) | k3_xboole_0(A_52, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_288])).
% 12.62/5.95  tff(c_1624, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1611, c_302])).
% 12.62/5.95  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.62/5.95  tff(c_1688, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1624, c_16])).
% 12.62/5.95  tff(c_1696, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1688])).
% 12.62/5.95  tff(c_6770, plain, (![A_171, B_172, C_173]: (k4_xboole_0(k3_xboole_0(A_171, B_172), C_173)=k3_xboole_0(B_172, k4_xboole_0(A_171, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_515])).
% 12.62/5.95  tff(c_22, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.62/5.95  tff(c_33184, plain, (![B_419, A_420, C_421]: (k3_xboole_0(B_419, k4_xboole_0(A_420, C_421))=k3_xboole_0(A_420, k4_xboole_0(B_419, C_421)))), inference(superposition, [status(thm), theory('equality')], [c_6770, c_22])).
% 12.62/5.95  tff(c_33999, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_33184, c_207])).
% 12.62/5.95  tff(c_34363, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1696, c_33999])).
% 12.62/5.95  tff(c_62, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.62/5.95  tff(c_78, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_62, c_24])).
% 12.62/5.95  tff(c_30, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.62/5.95  tff(c_1053, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.62/5.95  tff(c_1117, plain, (![A_30, C_83]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1053])).
% 12.62/5.95  tff(c_1131, plain, (![A_84, C_85]: (k5_xboole_0(A_84, k5_xboole_0(A_84, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1117])).
% 12.62/5.95  tff(c_1164, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1131])).
% 12.62/5.95  tff(c_1733, plain, (![B_98, A_99]: (k5_xboole_0(B_98, k3_xboole_0(A_99, B_98))=k4_xboole_0(B_98, A_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_228])).
% 12.62/5.95  tff(c_1130, plain, (![A_30, C_83]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1117])).
% 12.62/5.95  tff(c_14339, plain, (![B_288, A_289]: (k5_xboole_0(B_288, k4_xboole_0(B_288, A_289))=k3_xboole_0(A_289, B_288))), inference(superposition, [status(thm), theory('equality')], [c_1733, c_1130])).
% 12.62/5.95  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.62/5.95  tff(c_4120, plain, (![A_140, A_138, B_139]: (k5_xboole_0(A_140, k5_xboole_0(A_138, B_139))=k5_xboole_0(A_138, k5_xboole_0(B_139, A_140)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1053])).
% 12.62/5.95  tff(c_4353, plain, (![A_36, A_140]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_36, A_140))=k5_xboole_0(A_140, A_36))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4120])).
% 12.62/5.95  tff(c_14348, plain, (![B_288, A_289]: (k5_xboole_0(k4_xboole_0(B_288, A_289), B_288)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_289, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_14339, c_4353])).
% 12.62/5.95  tff(c_17002, plain, (![B_317, A_318]: (k5_xboole_0(k4_xboole_0(B_317, A_318), B_317)=k3_xboole_0(A_318, B_317))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_14348])).
% 12.62/5.95  tff(c_12469, plain, (![A_262, A_263]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_262, A_263))=k5_xboole_0(A_263, A_262))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4120])).
% 12.62/5.95  tff(c_1174, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1131])).
% 12.62/5.95  tff(c_12510, plain, (![A_262, A_263]: (k5_xboole_0(k5_xboole_0(A_262, A_263), k5_xboole_0(A_263, A_262))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12469, c_1174])).
% 12.62/5.95  tff(c_17008, plain, (![A_318, B_317]: (k5_xboole_0(k3_xboole_0(A_318, B_317), k5_xboole_0(B_317, k4_xboole_0(B_317, A_318)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17002, c_12510])).
% 12.62/5.95  tff(c_17135, plain, (![A_318, B_317]: (k5_xboole_0(k3_xboole_0(A_318, B_317), k3_xboole_0(B_317, A_318))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_17008])).
% 12.62/5.95  tff(c_34412, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34363, c_17135])).
% 12.62/5.95  tff(c_34571, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_247, c_2, c_34412])).
% 12.62/5.95  tff(c_34573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_34571])).
% 12.62/5.95  tff(c_34574, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 12.62/5.95  tff(c_34688, plain, (![A_430, B_431]: (k3_xboole_0(A_430, B_431)=A_430 | ~r1_tarski(A_430, B_431))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.62/5.95  tff(c_34700, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_34688])).
% 12.62/5.95  tff(c_34881, plain, (![A_443, B_444, C_445]: (k4_xboole_0(k3_xboole_0(A_443, B_444), C_445)=k3_xboole_0(A_443, k4_xboole_0(B_444, C_445)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.62/5.95  tff(c_35843, plain, (![A_470, B_471, C_472]: (r1_xboole_0(k3_xboole_0(A_470, k4_xboole_0(B_471, C_472)), C_472))), inference(superposition, [status(thm), theory('equality')], [c_34881, c_26])).
% 12.62/5.95  tff(c_35880, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34700, c_35843])).
% 12.62/5.95  tff(c_35898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34574, c_35880])).
% 12.62/5.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.62/5.95  
% 12.62/5.95  Inference rules
% 12.62/5.95  ----------------------
% 12.62/5.95  #Ref     : 0
% 12.62/5.95  #Sup     : 9081
% 12.62/5.95  #Fact    : 0
% 12.62/5.95  #Define  : 0
% 12.62/5.95  #Split   : 7
% 12.62/5.95  #Chain   : 0
% 12.62/5.95  #Close   : 0
% 12.62/5.95  
% 12.62/5.95  Ordering : KBO
% 12.62/5.95  
% 12.62/5.95  Simplification rules
% 12.62/5.95  ----------------------
% 12.62/5.95  #Subsume      : 319
% 12.62/5.95  #Demod        : 9121
% 12.62/5.95  #Tautology    : 5215
% 12.62/5.95  #SimpNegUnit  : 164
% 12.62/5.95  #BackRed      : 10
% 12.62/5.95  
% 12.62/5.95  #Partial instantiations: 0
% 12.62/5.95  #Strategies tried      : 1
% 12.62/5.95  
% 12.62/5.95  Timing (in seconds)
% 12.62/5.95  ----------------------
% 12.62/5.95  Preprocessing        : 0.29
% 12.62/5.95  Parsing              : 0.16
% 12.62/5.95  CNF conversion       : 0.02
% 12.62/5.95  Main loop            : 4.89
% 12.62/5.95  Inferencing          : 0.79
% 12.62/5.95  Reduction            : 3.00
% 12.62/5.95  Demodulation         : 2.70
% 12.62/5.95  BG Simplification    : 0.10
% 12.62/5.95  Subsumption          : 0.78
% 12.62/5.95  Abstraction          : 0.15
% 12.62/5.95  MUC search           : 0.00
% 12.62/5.95  Cooper               : 0.00
% 12.62/5.95  Total                : 5.22
% 12.62/5.95  Index Insertion      : 0.00
% 12.62/5.95  Index Deletion       : 0.00
% 12.62/5.95  Index Matching       : 0.00
% 12.62/5.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
