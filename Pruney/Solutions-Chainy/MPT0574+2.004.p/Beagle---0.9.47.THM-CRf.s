%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:51 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 131 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 157 expanded)
%              Number of equality atoms :   47 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_177,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_534,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(B_69,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_177])).

tff(c_30,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_540,plain,(
    ! [B_69,A_68] : k2_xboole_0(B_69,A_68) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_30])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_154])).

tff(c_32,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_215,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_32])).

tff(c_104,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,(
    ! [B_41] : k3_xboole_0(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_22])).

tff(c_231,plain,(
    ! [B_53] : k3_xboole_0(B_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_109])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_304,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_336,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_304])).

tff(c_343,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_336])).

tff(c_452,plain,(
    ! [A_63,B_64] : k2_xboole_0(A_63,k4_xboole_0(B_64,A_63)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_464,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = k2_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_452])).

tff(c_477,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_464])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,k3_xboole_0(B_8,C_9))
      | ~ r1_tarski(A_7,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_396,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_849,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,k3_xboole_0(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_10,c_396])).

tff(c_853,plain,(
    ! [B_8,C_9] :
      ( k3_xboole_0(B_8,C_9) = B_8
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(B_8,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_849])).

tff(c_883,plain,(
    ! [B_87,C_88] :
      ( k3_xboole_0(B_87,C_88) = B_87
      | ~ r1_tarski(B_87,C_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_853])).

tff(c_929,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_883])).

tff(c_198,plain,(
    ! [B_52,A_51] : k3_xboole_0(B_52,A_51) = k3_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_32])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1117,plain,(
    ! [A_95,B_96] : k3_xboole_0(k4_xboole_0(A_95,B_96),A_95) = k4_xboole_0(A_95,B_96) ),
    inference(resolution,[status(thm)],[c_14,c_883])).

tff(c_1163,plain,(
    ! [A_51,B_96] : k3_xboole_0(A_51,k4_xboole_0(A_51,B_96)) = k4_xboole_0(A_51,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_1117])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_307,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,k4_xboole_0(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_24])).

tff(c_1825,plain,(
    ! [A_111,B_112] : k4_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k4_xboole_0(A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_307])).

tff(c_1889,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_1825])).

tff(c_1926,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_1889])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1949,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_18])).

tff(c_1966,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_477,c_1949])).

tff(c_691,plain,(
    ! [C_76,A_77,B_78] :
      ( k2_xboole_0(k10_relat_1(C_76,A_77),k10_relat_1(C_76,B_78)) = k10_relat_1(C_76,k2_xboole_0(A_77,B_78))
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2783,plain,(
    ! [C_129,A_130,B_131] :
      ( r1_tarski(k10_relat_1(C_129,A_130),k10_relat_1(C_129,k2_xboole_0(A_130,B_131)))
      | ~ v1_relat_1(C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_26])).

tff(c_3010,plain,(
    ! [C_134] :
      ( r1_tarski(k10_relat_1(C_134,'#skF_1'),k10_relat_1(C_134,'#skF_2'))
      | ~ v1_relat_1(C_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1966,c_2783])).

tff(c_36,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3018,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3010,c_36])).

tff(c_3024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:54:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.71  
% 3.74/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.72  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.74/1.72  
% 3.74/1.72  %Foreground sorts:
% 3.74/1.72  
% 3.74/1.72  
% 3.74/1.72  %Background operators:
% 3.74/1.72  
% 3.74/1.72  
% 3.74/1.72  %Foreground operators:
% 3.74/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.74/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.74/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.74/1.72  
% 3.74/1.73  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 3.74/1.73  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.74/1.73  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.74/1.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.74/1.73  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.74/1.73  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.74/1.73  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.74/1.73  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.74/1.73  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.74/1.73  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.74/1.73  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.73  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.74/1.73  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.74/1.73  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 3.74/1.73  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.74/1.73  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.73  tff(c_28, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.74/1.73  tff(c_177, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.74/1.73  tff(c_534, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_28, c_177])).
% 3.74/1.73  tff(c_30, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.74/1.73  tff(c_540, plain, (![B_69, A_68]: (k2_xboole_0(B_69, A_68)=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_534, c_30])).
% 3.74/1.73  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.73  tff(c_154, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.73  tff(c_192, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_28, c_154])).
% 3.74/1.73  tff(c_32, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.73  tff(c_215, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_192, c_32])).
% 3.74/1.73  tff(c_104, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.73  tff(c_22, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.73  tff(c_109, plain, (![B_41]: (k3_xboole_0(k1_xboole_0, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_22])).
% 3.74/1.73  tff(c_231, plain, (![B_53]: (k3_xboole_0(B_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_109])).
% 3.74/1.73  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.74/1.73  tff(c_304, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.73  tff(c_336, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_304])).
% 3.74/1.73  tff(c_343, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_336])).
% 3.74/1.73  tff(c_452, plain, (![A_63, B_64]: (k2_xboole_0(A_63, k4_xboole_0(B_64, A_63))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.73  tff(c_464, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=k2_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_343, c_452])).
% 3.74/1.73  tff(c_477, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_464])).
% 3.74/1.73  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.73  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.73  tff(c_12, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, k3_xboole_0(B_8, C_9)) | ~r1_tarski(A_7, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.73  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.73  tff(c_396, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.73  tff(c_849, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, k3_xboole_0(A_85, B_86)))), inference(resolution, [status(thm)], [c_10, c_396])).
% 3.74/1.73  tff(c_853, plain, (![B_8, C_9]: (k3_xboole_0(B_8, C_9)=B_8 | ~r1_tarski(B_8, C_9) | ~r1_tarski(B_8, B_8))), inference(resolution, [status(thm)], [c_12, c_849])).
% 3.74/1.73  tff(c_883, plain, (![B_87, C_88]: (k3_xboole_0(B_87, C_88)=B_87 | ~r1_tarski(B_87, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_853])).
% 3.74/1.73  tff(c_929, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_883])).
% 3.74/1.73  tff(c_198, plain, (![B_52, A_51]: (k3_xboole_0(B_52, A_51)=k3_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_192, c_32])).
% 3.74/1.73  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.73  tff(c_1117, plain, (![A_95, B_96]: (k3_xboole_0(k4_xboole_0(A_95, B_96), A_95)=k4_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_14, c_883])).
% 3.74/1.73  tff(c_1163, plain, (![A_51, B_96]: (k3_xboole_0(A_51, k4_xboole_0(A_51, B_96))=k4_xboole_0(A_51, B_96))), inference(superposition, [status(thm), theory('equality')], [c_198, c_1117])).
% 3.74/1.73  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.73  tff(c_307, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k3_xboole_0(A_56, k4_xboole_0(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_304, c_24])).
% 3.74/1.73  tff(c_1825, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k4_xboole_0(A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_307])).
% 3.74/1.73  tff(c_1889, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_929, c_1825])).
% 3.74/1.73  tff(c_1926, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_343, c_1889])).
% 3.74/1.73  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.73  tff(c_1949, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1926, c_18])).
% 3.74/1.73  tff(c_1966, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_477, c_1949])).
% 3.74/1.73  tff(c_691, plain, (![C_76, A_77, B_78]: (k2_xboole_0(k10_relat_1(C_76, A_77), k10_relat_1(C_76, B_78))=k10_relat_1(C_76, k2_xboole_0(A_77, B_78)) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.74/1.73  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.74/1.73  tff(c_2783, plain, (![C_129, A_130, B_131]: (r1_tarski(k10_relat_1(C_129, A_130), k10_relat_1(C_129, k2_xboole_0(A_130, B_131))) | ~v1_relat_1(C_129))), inference(superposition, [status(thm), theory('equality')], [c_691, c_26])).
% 3.74/1.73  tff(c_3010, plain, (![C_134]: (r1_tarski(k10_relat_1(C_134, '#skF_1'), k10_relat_1(C_134, '#skF_2')) | ~v1_relat_1(C_134))), inference(superposition, [status(thm), theory('equality')], [c_1966, c_2783])).
% 3.74/1.73  tff(c_36, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.73  tff(c_3018, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3010, c_36])).
% 3.74/1.73  tff(c_3024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3018])).
% 3.74/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.73  
% 3.74/1.73  Inference rules
% 3.74/1.73  ----------------------
% 3.74/1.73  #Ref     : 0
% 3.74/1.73  #Sup     : 736
% 3.74/1.73  #Fact    : 0
% 3.74/1.73  #Define  : 0
% 3.74/1.73  #Split   : 1
% 3.74/1.73  #Chain   : 0
% 3.74/1.73  #Close   : 0
% 3.74/1.73  
% 3.74/1.73  Ordering : KBO
% 3.74/1.73  
% 3.74/1.73  Simplification rules
% 3.74/1.73  ----------------------
% 3.74/1.73  #Subsume      : 38
% 3.74/1.73  #Demod        : 617
% 3.74/1.73  #Tautology    : 558
% 3.74/1.73  #SimpNegUnit  : 0
% 3.74/1.73  #BackRed      : 0
% 3.74/1.73  
% 3.74/1.73  #Partial instantiations: 0
% 3.74/1.73  #Strategies tried      : 1
% 3.74/1.73  
% 3.74/1.73  Timing (in seconds)
% 3.74/1.73  ----------------------
% 3.94/1.73  Preprocessing        : 0.31
% 3.94/1.73  Parsing              : 0.18
% 3.94/1.73  CNF conversion       : 0.02
% 3.94/1.73  Main loop            : 0.60
% 3.94/1.73  Inferencing          : 0.21
% 3.94/1.73  Reduction            : 0.25
% 3.94/1.73  Demodulation         : 0.20
% 3.94/1.73  BG Simplification    : 0.02
% 3.94/1.73  Subsumption          : 0.09
% 3.94/1.73  Abstraction          : 0.03
% 3.94/1.73  MUC search           : 0.00
% 3.94/1.73  Cooper               : 0.00
% 3.94/1.73  Total                : 0.95
% 3.94/1.73  Index Insertion      : 0.00
% 3.94/1.73  Index Deletion       : 0.00
% 3.94/1.73  Index Matching       : 0.00
% 3.94/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
