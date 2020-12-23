%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   70 (  82 expanded)
%              Number of leaves         :   36 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :   48 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [D_48,C_47,A_45,B_46,E_49,F_50] : k5_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50) = k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [G_57,B_52,E_55,F_56,C_53,D_54,A_51] : k6_enumset1(A_51,A_51,B_52,C_53,D_54,E_55,F_56,G_57) = k5_enumset1(A_51,B_52,C_53,D_54,E_55,F_56,G_57) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1753,plain,(
    ! [G_3746,F_3745,C_3743,A_3742,D_3748,B_3749,E_3744,H_3747] : k2_xboole_0(k5_enumset1(A_3742,B_3749,C_3743,D_3748,E_3744,F_3745,G_3746),k1_tarski(H_3747)) = k6_enumset1(A_3742,B_3749,C_3743,D_3748,E_3744,F_3745,G_3746,H_3747) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1762,plain,(
    ! [D_48,C_47,A_45,B_46,H_3747,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,H_3747) = k2_xboole_0(k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50),k1_tarski(H_3747)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1753])).

tff(c_2181,plain,(
    ! [E_4044,H_4045,D_4042,C_4043,F_4046,A_4041,B_4040] : k2_xboole_0(k4_enumset1(A_4041,B_4040,C_4043,D_4042,E_4044,F_4046),k1_tarski(H_4045)) = k5_enumset1(A_4041,B_4040,C_4043,D_4042,E_4044,F_4046,H_4045) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1762])).

tff(c_2190,plain,(
    ! [E_44,C_42,H_4045,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,H_4045) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_tarski(H_4045)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2181])).

tff(c_2244,plain,(
    ! [D_4105,A_4104,E_4103,H_4107,B_4108,C_4106] : k2_xboole_0(k3_enumset1(A_4104,B_4108,C_4106,D_4105,E_4103),k1_tarski(H_4107)) = k4_enumset1(A_4104,B_4108,C_4106,D_4105,E_4103,H_4107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2190])).

tff(c_2303,plain,(
    ! [D_39,A_36,H_4107,C_38,B_37] : k4_enumset1(A_36,A_36,B_37,C_38,D_39,H_4107) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),k1_tarski(H_4107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2244])).

tff(c_2307,plain,(
    ! [A_4166,B_4168,D_4167,C_4169,H_4165] : k2_xboole_0(k2_enumset1(A_4166,B_4168,C_4169,D_4167),k1_tarski(H_4165)) = k3_enumset1(A_4166,B_4168,C_4169,D_4167,H_4165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2303])).

tff(c_2375,plain,(
    ! [A_33,B_34,C_35,H_4165] : k3_enumset1(A_33,A_33,B_34,C_35,H_4165) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),k1_tarski(H_4165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2307])).

tff(c_2381,plain,(
    ! [A_4286,B_4287,C_4288,H_4289] : k2_xboole_0(k1_enumset1(A_4286,B_4287,C_4288),k1_tarski(H_4289)) = k2_enumset1(A_4286,B_4287,C_4288,H_4289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2375])).

tff(c_2446,plain,(
    ! [A_31,B_32,H_4289] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(H_4289)) = k2_enumset1(A_31,A_31,B_32,H_4289) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2381])).

tff(c_2450,plain,(
    ! [A_4346,B_4347,H_4348] : k2_xboole_0(k2_tarski(A_4346,B_4347),k1_tarski(H_4348)) = k1_enumset1(A_4346,B_4347,H_4348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2446])).

tff(c_2509,plain,(
    ! [A_30,H_4348] : k2_xboole_0(k1_tarski(A_30),k1_tarski(H_4348)) = k1_enumset1(A_30,A_30,H_4348) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2450])).

tff(c_2513,plain,(
    ! [A_4405,H_4406] : k2_xboole_0(k1_tarski(A_4405),k1_tarski(H_4406)) = k2_tarski(A_4405,H_4406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2509])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_135,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_135])).

tff(c_147,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_144])).

tff(c_2519,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2513,c_147])).

tff(c_97,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    ! [B_73,A_72] : r2_hidden(B_73,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_10])).

tff(c_2646,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_109])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2686,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2646,c_32])).

tff(c_2729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.82  
% 4.59/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.82  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.59/1.82  
% 4.59/1.82  %Foreground sorts:
% 4.59/1.82  
% 4.59/1.82  
% 4.59/1.82  %Background operators:
% 4.59/1.82  
% 4.59/1.82  
% 4.59/1.82  %Foreground operators:
% 4.59/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.59/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.59/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.59/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.59/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.59/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.59/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.59/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.59/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.59/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.59/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.59/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.59/1.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.59/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.59/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.59/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.59/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.59/1.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.59/1.82  
% 4.72/1.84  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 4.72/1.84  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.72/1.84  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.72/1.84  tff(f_63, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.72/1.84  tff(f_65, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.72/1.84  tff(f_67, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.72/1.84  tff(f_69, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.72/1.84  tff(f_71, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.72/1.84  tff(f_57, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 4.72/1.84  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.72/1.84  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.72/1.84  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.72/1.84  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.72/1.84  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.72/1.84  tff(c_50, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.84  tff(c_48, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.72/1.84  tff(c_52, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.84  tff(c_54, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.72/1.84  tff(c_56, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.72/1.84  tff(c_58, plain, (![D_48, C_47, A_45, B_46, E_49, F_50]: (k5_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50)=k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.84  tff(c_60, plain, (![G_57, B_52, E_55, F_56, C_53, D_54, A_51]: (k6_enumset1(A_51, A_51, B_52, C_53, D_54, E_55, F_56, G_57)=k5_enumset1(A_51, B_52, C_53, D_54, E_55, F_56, G_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.72/1.84  tff(c_1753, plain, (![G_3746, F_3745, C_3743, A_3742, D_3748, B_3749, E_3744, H_3747]: (k2_xboole_0(k5_enumset1(A_3742, B_3749, C_3743, D_3748, E_3744, F_3745, G_3746), k1_tarski(H_3747))=k6_enumset1(A_3742, B_3749, C_3743, D_3748, E_3744, F_3745, G_3746, H_3747))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.72/1.84  tff(c_1762, plain, (![D_48, C_47, A_45, B_46, H_3747, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, H_3747)=k2_xboole_0(k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50), k1_tarski(H_3747)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1753])).
% 4.72/1.84  tff(c_2181, plain, (![E_4044, H_4045, D_4042, C_4043, F_4046, A_4041, B_4040]: (k2_xboole_0(k4_enumset1(A_4041, B_4040, C_4043, D_4042, E_4044, F_4046), k1_tarski(H_4045))=k5_enumset1(A_4041, B_4040, C_4043, D_4042, E_4044, F_4046, H_4045))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1762])).
% 4.72/1.84  tff(c_2190, plain, (![E_44, C_42, H_4045, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, H_4045)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_tarski(H_4045)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2181])).
% 4.72/1.84  tff(c_2244, plain, (![D_4105, A_4104, E_4103, H_4107, B_4108, C_4106]: (k2_xboole_0(k3_enumset1(A_4104, B_4108, C_4106, D_4105, E_4103), k1_tarski(H_4107))=k4_enumset1(A_4104, B_4108, C_4106, D_4105, E_4103, H_4107))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2190])).
% 4.72/1.84  tff(c_2303, plain, (![D_39, A_36, H_4107, C_38, B_37]: (k4_enumset1(A_36, A_36, B_37, C_38, D_39, H_4107)=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), k1_tarski(H_4107)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2244])).
% 4.72/1.84  tff(c_2307, plain, (![A_4166, B_4168, D_4167, C_4169, H_4165]: (k2_xboole_0(k2_enumset1(A_4166, B_4168, C_4169, D_4167), k1_tarski(H_4165))=k3_enumset1(A_4166, B_4168, C_4169, D_4167, H_4165))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2303])).
% 4.72/1.84  tff(c_2375, plain, (![A_33, B_34, C_35, H_4165]: (k3_enumset1(A_33, A_33, B_34, C_35, H_4165)=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), k1_tarski(H_4165)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2307])).
% 4.72/1.84  tff(c_2381, plain, (![A_4286, B_4287, C_4288, H_4289]: (k2_xboole_0(k1_enumset1(A_4286, B_4287, C_4288), k1_tarski(H_4289))=k2_enumset1(A_4286, B_4287, C_4288, H_4289))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2375])).
% 4.72/1.84  tff(c_2446, plain, (![A_31, B_32, H_4289]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(H_4289))=k2_enumset1(A_31, A_31, B_32, H_4289))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2381])).
% 4.72/1.84  tff(c_2450, plain, (![A_4346, B_4347, H_4348]: (k2_xboole_0(k2_tarski(A_4346, B_4347), k1_tarski(H_4348))=k1_enumset1(A_4346, B_4347, H_4348))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2446])).
% 4.72/1.84  tff(c_2509, plain, (![A_30, H_4348]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(H_4348))=k1_enumset1(A_30, A_30, H_4348))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2450])).
% 4.72/1.84  tff(c_2513, plain, (![A_4405, H_4406]: (k2_xboole_0(k1_tarski(A_4405), k1_tarski(H_4406))=k2_tarski(A_4405, H_4406))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2509])).
% 4.72/1.84  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.72/1.84  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.72/1.84  tff(c_135, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.84  tff(c_144, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_135])).
% 4.72/1.84  tff(c_147, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_144])).
% 4.72/1.84  tff(c_2519, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2513, c_147])).
% 4.72/1.84  tff(c_97, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.84  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/1.84  tff(c_109, plain, (![B_73, A_72]: (r2_hidden(B_73, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_10])).
% 4.72/1.84  tff(c_2646, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2519, c_109])).
% 4.72/1.84  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.72/1.84  tff(c_2686, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2646, c_32])).
% 4.72/1.84  tff(c_2729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2686])).
% 4.72/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.84  
% 4.72/1.84  Inference rules
% 4.72/1.84  ----------------------
% 4.72/1.84  #Ref     : 0
% 4.72/1.84  #Sup     : 372
% 4.72/1.84  #Fact    : 4
% 4.72/1.84  #Define  : 0
% 4.72/1.84  #Split   : 6
% 4.72/1.84  #Chain   : 0
% 4.72/1.84  #Close   : 0
% 4.72/1.84  
% 4.72/1.84  Ordering : KBO
% 4.72/1.84  
% 4.72/1.84  Simplification rules
% 4.72/1.84  ----------------------
% 4.72/1.84  #Subsume      : 45
% 4.72/1.84  #Demod        : 52
% 4.72/1.84  #Tautology    : 182
% 4.72/1.84  #SimpNegUnit  : 1
% 4.72/1.84  #BackRed      : 0
% 4.72/1.84  
% 4.72/1.84  #Partial instantiations: 1444
% 4.72/1.84  #Strategies tried      : 1
% 4.72/1.84  
% 4.72/1.84  Timing (in seconds)
% 4.72/1.84  ----------------------
% 4.72/1.84  Preprocessing        : 0.34
% 4.72/1.84  Parsing              : 0.17
% 4.72/1.84  CNF conversion       : 0.03
% 4.72/1.84  Main loop            : 0.74
% 4.72/1.84  Inferencing          : 0.37
% 4.72/1.84  Reduction            : 0.17
% 4.72/1.84  Demodulation         : 0.12
% 4.72/1.84  BG Simplification    : 0.04
% 4.72/1.84  Subsumption          : 0.13
% 4.72/1.84  Abstraction          : 0.04
% 4.72/1.84  MUC search           : 0.00
% 4.72/1.84  Cooper               : 0.00
% 4.72/1.84  Total                : 1.12
% 4.72/1.84  Index Insertion      : 0.00
% 4.72/1.84  Index Deletion       : 0.00
% 4.72/1.84  Index Matching       : 0.00
% 4.72/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
