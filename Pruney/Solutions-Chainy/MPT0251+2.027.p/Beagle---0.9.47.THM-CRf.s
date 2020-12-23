%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 162 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  108 ( 206 expanded)
%              Number of equality atoms :   43 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_68,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_541,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,A_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_773,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_123,B_124)),A_123)
      | v1_xboole_0(k4_xboole_0(A_123,B_124)) ) ),
    inference(resolution,[status(thm)],[c_4,c_541])).

tff(c_202,plain,(
    ! [D_60,B_61,A_62] :
      ( ~ r2_hidden(D_60,B_61)
      | ~ r2_hidden(D_60,k4_xboole_0(A_62,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [A_62,B_61] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_62,B_61)),B_61)
      | v1_xboole_0(k4_xboole_0(A_62,B_61)) ) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_804,plain,(
    ! [A_123] : v1_xboole_0(k4_xboole_0(A_123,A_123)) ),
    inference(resolution,[status(thm)],[c_773,c_207])).

tff(c_48,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_389,plain,(
    ! [B_72,C_73,A_74] :
      ( r2_hidden(B_72,C_73)
      | ~ r1_tarski(k2_tarski(A_74,B_72),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_443,plain,(
    ! [B_77,A_78] : r2_hidden(B_77,k2_tarski(A_78,B_77)) ),
    inference(resolution,[status(thm)],[c_36,c_389])).

tff(c_449,plain,(
    ! [B_26,A_25] : r2_hidden(B_26,k2_tarski(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_443])).

tff(c_150,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_237,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_150])).

tff(c_58,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_274,plain,(
    ! [B_69,A_70] : k2_xboole_0(B_69,A_70) = k2_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_58])).

tff(c_290,plain,(
    ! [A_70] : k2_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_40])).

tff(c_321,plain,(
    ! [A_71] : k2_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_40])).

tff(c_46,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_334,plain,(
    ! [B_24] : k4_xboole_0(B_24,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_46])).

tff(c_404,plain,(
    ! [B_75] : k4_xboole_0(B_75,k1_xboole_0) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_334])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_511,plain,(
    ! [D_90,B_91] :
      ( ~ r2_hidden(D_90,k1_xboole_0)
      | ~ r2_hidden(D_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_8])).

tff(c_515,plain,(
    ! [B_91] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_91)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_511])).

tff(c_517,plain,(
    ! [B_92] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_92) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_532,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_449,c_517])).

tff(c_533,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_914,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_4'(A_141,B_142),B_142)
      | r2_hidden('#skF_5'(A_141,B_142),A_141)
      | B_142 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_960,plain,(
    ! [B_143,A_144] :
      ( ~ v1_xboole_0(B_143)
      | r2_hidden('#skF_5'(A_144,B_143),A_144)
      | B_143 = A_144 ) ),
    inference(resolution,[status(thm)],[c_914,c_2])).

tff(c_989,plain,(
    ! [A_145,B_146] :
      ( ~ v1_xboole_0(A_145)
      | ~ v1_xboole_0(B_146)
      | B_146 = A_145 ) ),
    inference(resolution,[status(thm)],[c_960,c_2])).

tff(c_999,plain,(
    ! [B_147] :
      ( ~ v1_xboole_0(B_147)
      | k1_xboole_0 = B_147 ) ),
    inference(resolution,[status(thm)],[c_533,c_989])).

tff(c_1010,plain,(
    ! [A_123] : k4_xboole_0(A_123,A_123) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_804,c_999])).

tff(c_185,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_189,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_551,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_563,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_551])).

tff(c_50,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_675,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(k2_tarski(A_109,B_110),C_111)
      | ~ r2_hidden(B_110,C_111)
      | ~ r2_hidden(A_109,C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_700,plain,(
    ! [A_112,C_113] :
      ( r1_tarski(k1_tarski(A_112),C_113)
      | ~ r2_hidden(A_112,C_113)
      | ~ r2_hidden(A_112,C_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_675])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_712,plain,(
    ! [A_114,C_115] :
      ( k3_xboole_0(k1_tarski(A_114),C_115) = k1_tarski(A_114)
      | ~ r2_hidden(A_114,C_115) ) ),
    inference(resolution,[status(thm)],[c_700,c_44])).

tff(c_38,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_718,plain,(
    ! [A_114,C_115] :
      ( k5_xboole_0(k1_tarski(A_114),k1_tarski(A_114)) = k4_xboole_0(k1_tarski(A_114),C_115)
      | ~ r2_hidden(A_114,C_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_38])).

tff(c_734,plain,(
    ! [A_114,C_115] :
      ( k4_xboole_0(k1_tarski(A_114),k1_tarski(A_114)) = k4_xboole_0(k1_tarski(A_114),C_115)
      | ~ r2_hidden(A_114,C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_718])).

tff(c_2691,plain,(
    ! [A_261,C_262] :
      ( k4_xboole_0(k1_tarski(A_261),C_262) = k1_xboole_0
      | ~ r2_hidden(A_261,C_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_734])).

tff(c_2758,plain,(
    ! [C_262,A_261] :
      ( k2_xboole_0(C_262,k1_tarski(A_261)) = k2_xboole_0(C_262,k1_xboole_0)
      | ~ r2_hidden(A_261,C_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2691,c_46])).

tff(c_2795,plain,(
    ! [C_263,A_264] :
      ( k2_xboole_0(C_263,k1_tarski(A_264)) = C_263
      | ~ r2_hidden(A_264,C_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2758])).

tff(c_243,plain,(
    ! [B_66,A_65] : k2_xboole_0(B_66,A_65) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_58])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_273,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_66])).

tff(c_2809,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2795,c_273])).

tff(c_2855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.74  
% 3.83/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.74  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 3.83/1.74  
% 3.83/1.74  %Foreground sorts:
% 3.83/1.74  
% 3.83/1.74  
% 3.83/1.74  %Background operators:
% 3.83/1.74  
% 3.83/1.74  
% 3.83/1.74  %Foreground operators:
% 3.83/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.83/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.83/1.74  tff('#skF_7', type, '#skF_7': $i).
% 3.83/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.83/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.83/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.83/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.83/1.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.83/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.74  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.83/1.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.83/1.74  
% 3.83/1.77  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.83/1.77  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.83/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.83/1.77  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.83/1.77  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.83/1.77  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.83/1.77  tff(f_84, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.83/1.77  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.83/1.77  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.83/1.77  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.83/1.77  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.83/1.77  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.83/1.77  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.83/1.77  tff(c_68, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.77  tff(c_40, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.77  tff(c_541, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, A_96) | ~r2_hidden(D_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.83/1.77  tff(c_773, plain, (![A_123, B_124]: (r2_hidden('#skF_1'(k4_xboole_0(A_123, B_124)), A_123) | v1_xboole_0(k4_xboole_0(A_123, B_124)))), inference(resolution, [status(thm)], [c_4, c_541])).
% 3.83/1.77  tff(c_202, plain, (![D_60, B_61, A_62]: (~r2_hidden(D_60, B_61) | ~r2_hidden(D_60, k4_xboole_0(A_62, B_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.83/1.77  tff(c_207, plain, (![A_62, B_61]: (~r2_hidden('#skF_1'(k4_xboole_0(A_62, B_61)), B_61) | v1_xboole_0(k4_xboole_0(A_62, B_61)))), inference(resolution, [status(thm)], [c_4, c_202])).
% 3.83/1.77  tff(c_804, plain, (![A_123]: (v1_xboole_0(k4_xboole_0(A_123, A_123)))), inference(resolution, [status(thm)], [c_773, c_207])).
% 3.83/1.77  tff(c_48, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.83/1.77  tff(c_36, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/1.77  tff(c_389, plain, (![B_72, C_73, A_74]: (r2_hidden(B_72, C_73) | ~r1_tarski(k2_tarski(A_74, B_72), C_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.83/1.77  tff(c_443, plain, (![B_77, A_78]: (r2_hidden(B_77, k2_tarski(A_78, B_77)))), inference(resolution, [status(thm)], [c_36, c_389])).
% 3.83/1.77  tff(c_449, plain, (![B_26, A_25]: (r2_hidden(B_26, k2_tarski(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_443])).
% 3.83/1.77  tff(c_150, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.83/1.77  tff(c_237, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_48, c_150])).
% 3.83/1.77  tff(c_58, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.83/1.77  tff(c_274, plain, (![B_69, A_70]: (k2_xboole_0(B_69, A_70)=k2_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_237, c_58])).
% 3.83/1.77  tff(c_290, plain, (![A_70]: (k2_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_274, c_40])).
% 3.83/1.77  tff(c_321, plain, (![A_71]: (k2_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_274, c_40])).
% 3.83/1.77  tff(c_46, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.83/1.77  tff(c_334, plain, (![B_24]: (k4_xboole_0(B_24, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_24))), inference(superposition, [status(thm), theory('equality')], [c_321, c_46])).
% 3.83/1.77  tff(c_404, plain, (![B_75]: (k4_xboole_0(B_75, k1_xboole_0)=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_334])).
% 3.83/1.77  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.83/1.77  tff(c_511, plain, (![D_90, B_91]: (~r2_hidden(D_90, k1_xboole_0) | ~r2_hidden(D_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_404, c_8])).
% 3.83/1.77  tff(c_515, plain, (![B_91]: (~r2_hidden('#skF_1'(k1_xboole_0), B_91) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_511])).
% 3.83/1.77  tff(c_517, plain, (![B_92]: (~r2_hidden('#skF_1'(k1_xboole_0), B_92))), inference(splitLeft, [status(thm)], [c_515])).
% 3.83/1.77  tff(c_532, plain, $false, inference(resolution, [status(thm)], [c_449, c_517])).
% 3.83/1.77  tff(c_533, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_515])).
% 3.83/1.77  tff(c_914, plain, (![A_141, B_142]: (r2_hidden('#skF_4'(A_141, B_142), B_142) | r2_hidden('#skF_5'(A_141, B_142), A_141) | B_142=A_141)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.83/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.77  tff(c_960, plain, (![B_143, A_144]: (~v1_xboole_0(B_143) | r2_hidden('#skF_5'(A_144, B_143), A_144) | B_143=A_144)), inference(resolution, [status(thm)], [c_914, c_2])).
% 3.83/1.77  tff(c_989, plain, (![A_145, B_146]: (~v1_xboole_0(A_145) | ~v1_xboole_0(B_146) | B_146=A_145)), inference(resolution, [status(thm)], [c_960, c_2])).
% 3.83/1.77  tff(c_999, plain, (![B_147]: (~v1_xboole_0(B_147) | k1_xboole_0=B_147)), inference(resolution, [status(thm)], [c_533, c_989])).
% 3.83/1.77  tff(c_1010, plain, (![A_123]: (k4_xboole_0(A_123, A_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_804, c_999])).
% 3.83/1.77  tff(c_185, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.83/1.77  tff(c_189, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_36, c_185])).
% 3.83/1.77  tff(c_551, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.83/1.77  tff(c_563, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_189, c_551])).
% 3.83/1.77  tff(c_50, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.83/1.77  tff(c_675, plain, (![A_109, B_110, C_111]: (r1_tarski(k2_tarski(A_109, B_110), C_111) | ~r2_hidden(B_110, C_111) | ~r2_hidden(A_109, C_111))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.83/1.77  tff(c_700, plain, (![A_112, C_113]: (r1_tarski(k1_tarski(A_112), C_113) | ~r2_hidden(A_112, C_113) | ~r2_hidden(A_112, C_113))), inference(superposition, [status(thm), theory('equality')], [c_50, c_675])).
% 3.83/1.77  tff(c_44, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.83/1.77  tff(c_712, plain, (![A_114, C_115]: (k3_xboole_0(k1_tarski(A_114), C_115)=k1_tarski(A_114) | ~r2_hidden(A_114, C_115))), inference(resolution, [status(thm)], [c_700, c_44])).
% 3.83/1.77  tff(c_38, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.83/1.77  tff(c_718, plain, (![A_114, C_115]: (k5_xboole_0(k1_tarski(A_114), k1_tarski(A_114))=k4_xboole_0(k1_tarski(A_114), C_115) | ~r2_hidden(A_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_712, c_38])).
% 3.83/1.77  tff(c_734, plain, (![A_114, C_115]: (k4_xboole_0(k1_tarski(A_114), k1_tarski(A_114))=k4_xboole_0(k1_tarski(A_114), C_115) | ~r2_hidden(A_114, C_115))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_718])).
% 3.83/1.77  tff(c_2691, plain, (![A_261, C_262]: (k4_xboole_0(k1_tarski(A_261), C_262)=k1_xboole_0 | ~r2_hidden(A_261, C_262))), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_734])).
% 3.83/1.77  tff(c_2758, plain, (![C_262, A_261]: (k2_xboole_0(C_262, k1_tarski(A_261))=k2_xboole_0(C_262, k1_xboole_0) | ~r2_hidden(A_261, C_262))), inference(superposition, [status(thm), theory('equality')], [c_2691, c_46])).
% 3.83/1.77  tff(c_2795, plain, (![C_263, A_264]: (k2_xboole_0(C_263, k1_tarski(A_264))=C_263 | ~r2_hidden(A_264, C_263))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2758])).
% 3.83/1.77  tff(c_243, plain, (![B_66, A_65]: (k2_xboole_0(B_66, A_65)=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_237, c_58])).
% 3.83/1.77  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_6'), '#skF_7')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.77  tff(c_273, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_66])).
% 3.83/1.77  tff(c_2809, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2795, c_273])).
% 3.83/1.77  tff(c_2855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2809])).
% 3.83/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.77  
% 3.83/1.77  Inference rules
% 3.83/1.77  ----------------------
% 3.83/1.77  #Ref     : 0
% 3.83/1.77  #Sup     : 660
% 3.83/1.77  #Fact    : 0
% 3.83/1.77  #Define  : 0
% 3.83/1.77  #Split   : 1
% 3.83/1.77  #Chain   : 0
% 3.83/1.77  #Close   : 0
% 3.83/1.77  
% 3.83/1.77  Ordering : KBO
% 3.83/1.77  
% 3.83/1.77  Simplification rules
% 3.83/1.77  ----------------------
% 3.83/1.77  #Subsume      : 197
% 3.83/1.77  #Demod        : 256
% 3.83/1.77  #Tautology    : 272
% 3.83/1.77  #SimpNegUnit  : 3
% 3.83/1.77  #BackRed      : 5
% 3.83/1.77  
% 3.83/1.77  #Partial instantiations: 0
% 3.83/1.77  #Strategies tried      : 1
% 3.83/1.77  
% 3.83/1.77  Timing (in seconds)
% 3.83/1.77  ----------------------
% 3.83/1.77  Preprocessing        : 0.31
% 3.83/1.77  Parsing              : 0.16
% 3.83/1.77  CNF conversion       : 0.03
% 3.83/1.77  Main loop            : 0.60
% 3.83/1.77  Inferencing          : 0.22
% 3.83/1.77  Reduction            : 0.20
% 3.83/1.77  Demodulation         : 0.15
% 3.83/1.77  BG Simplification    : 0.03
% 3.83/1.77  Subsumption          : 0.12
% 3.83/1.77  Abstraction          : 0.04
% 3.83/1.77  MUC search           : 0.00
% 3.83/1.77  Cooper               : 0.00
% 3.83/1.77  Total                : 0.96
% 3.83/1.77  Index Insertion      : 0.00
% 3.83/1.77  Index Deletion       : 0.00
% 3.83/1.77  Index Matching       : 0.00
% 3.83/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
