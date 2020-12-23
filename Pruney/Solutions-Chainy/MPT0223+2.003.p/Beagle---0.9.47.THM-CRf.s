%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   76 (  88 expanded)
%              Number of leaves         :   38 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :   61 (  74 expanded)
%              Number of equality atoms :   54 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49) = k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [A_50,B_51,G_56,E_54,C_52,D_53,F_55] : k6_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,G_56) = k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,G_56) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2184,plain,(
    ! [A_3852,E_3858,B_3857,D_3853,H_3854,G_3851,C_3855,F_3856] : k2_xboole_0(k5_enumset1(A_3852,B_3857,C_3855,D_3853,E_3858,F_3856,G_3851),k1_tarski(H_3854)) = k6_enumset1(A_3852,B_3857,C_3855,D_3853,E_3858,F_3856,G_3851,H_3854) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2193,plain,(
    ! [C_46,E_48,F_49,A_44,H_3854,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,H_3854) = k2_xboole_0(k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49),k1_tarski(H_3854)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2184])).

tff(c_2512,plain,(
    ! [C_4094,F_4092,A_4096,E_4091,B_4095,D_4093,H_4097] : k2_xboole_0(k4_enumset1(A_4096,B_4095,C_4094,D_4093,E_4091,F_4092),k1_tarski(H_4097)) = k5_enumset1(A_4096,B_4095,C_4094,D_4093,E_4091,F_4092,H_4097) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2193])).

tff(c_2521,plain,(
    ! [E_43,D_42,A_39,C_41,B_40,H_4097] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,H_4097) = k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k1_tarski(H_4097)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2512])).

tff(c_2575,plain,(
    ! [D_4157,C_4156,B_4155,E_4159,A_4154,H_4158] : k2_xboole_0(k3_enumset1(A_4154,B_4155,C_4156,D_4157,E_4159),k1_tarski(H_4158)) = k4_enumset1(A_4154,B_4155,C_4156,D_4157,E_4159,H_4158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2521])).

tff(c_2634,plain,(
    ! [A_35,B_36,C_37,D_38,H_4158] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,H_4158) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(H_4158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2575])).

tff(c_2638,plain,(
    ! [C_4218,H_4217,B_4220,D_4219,A_4216] : k2_xboole_0(k2_enumset1(A_4216,B_4220,C_4218,D_4219),k1_tarski(H_4217)) = k3_enumset1(A_4216,B_4220,C_4218,D_4219,H_4217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2634])).

tff(c_2697,plain,(
    ! [A_32,B_33,C_34,H_4217] : k3_enumset1(A_32,A_32,B_33,C_34,H_4217) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(H_4217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2638])).

tff(c_2703,plain,(
    ! [A_4337,B_4338,C_4339,H_4340] : k2_xboole_0(k1_enumset1(A_4337,B_4338,C_4339),k1_tarski(H_4340)) = k2_enumset1(A_4337,B_4338,C_4339,H_4340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2697])).

tff(c_2762,plain,(
    ! [A_30,B_31,H_4340] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(H_4340)) = k2_enumset1(A_30,A_30,B_31,H_4340) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2703])).

tff(c_2766,plain,(
    ! [A_4397,B_4398,H_4399] : k2_xboole_0(k2_tarski(A_4397,B_4398),k1_tarski(H_4399)) = k1_enumset1(A_4397,B_4398,H_4399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2762])).

tff(c_2831,plain,(
    ! [A_29,H_4399] : k2_xboole_0(k1_tarski(A_29),k1_tarski(H_4399)) = k1_enumset1(A_29,A_29,H_4399) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2766])).

tff(c_2835,plain,(
    ! [A_4456,H_4457] : k2_xboole_0(k1_tarski(A_4456),k1_tarski(H_4457)) = k2_tarski(A_4456,H_4457) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2831])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_192,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_192])).

tff(c_204,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_201])).

tff(c_211,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_220,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_211])).

tff(c_223,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_220])).

tff(c_2841,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2835,c_223])).

tff(c_149,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_161,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_14])).

tff(c_2983,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_161])).

tff(c_36,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3027,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2983,c_36])).

tff(c_3070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.80  
% 4.45/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.80  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.45/1.80  
% 4.45/1.80  %Foreground sorts:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Background operators:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Foreground operators:
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.45/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.45/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.45/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.45/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.45/1.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.45/1.80  
% 4.50/1.81  tff(f_78, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.50/1.81  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.50/1.81  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.50/1.81  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.50/1.81  tff(f_67, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.50/1.81  tff(f_69, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.50/1.81  tff(f_71, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.50/1.81  tff(f_73, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.50/1.81  tff(f_59, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 4.50/1.81  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.50/1.81  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.50/1.81  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.81  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.50/1.81  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.50/1.81  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.50/1.81  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.50/1.81  tff(c_52, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.50/1.81  tff(c_50, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.50/1.81  tff(c_54, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.50/1.81  tff(c_56, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.50/1.81  tff(c_58, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.50/1.81  tff(c_60, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.50/1.81  tff(c_62, plain, (![A_50, B_51, G_56, E_54, C_52, D_53, F_55]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56)=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.81  tff(c_2184, plain, (![A_3852, E_3858, B_3857, D_3853, H_3854, G_3851, C_3855, F_3856]: (k2_xboole_0(k5_enumset1(A_3852, B_3857, C_3855, D_3853, E_3858, F_3856, G_3851), k1_tarski(H_3854))=k6_enumset1(A_3852, B_3857, C_3855, D_3853, E_3858, F_3856, G_3851, H_3854))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.50/1.81  tff(c_2193, plain, (![C_46, E_48, F_49, A_44, H_3854, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, H_3854)=k2_xboole_0(k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49), k1_tarski(H_3854)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2184])).
% 4.50/1.81  tff(c_2512, plain, (![C_4094, F_4092, A_4096, E_4091, B_4095, D_4093, H_4097]: (k2_xboole_0(k4_enumset1(A_4096, B_4095, C_4094, D_4093, E_4091, F_4092), k1_tarski(H_4097))=k5_enumset1(A_4096, B_4095, C_4094, D_4093, E_4091, F_4092, H_4097))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2193])).
% 4.50/1.81  tff(c_2521, plain, (![E_43, D_42, A_39, C_41, B_40, H_4097]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, H_4097)=k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k1_tarski(H_4097)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2512])).
% 4.50/1.81  tff(c_2575, plain, (![D_4157, C_4156, B_4155, E_4159, A_4154, H_4158]: (k2_xboole_0(k3_enumset1(A_4154, B_4155, C_4156, D_4157, E_4159), k1_tarski(H_4158))=k4_enumset1(A_4154, B_4155, C_4156, D_4157, E_4159, H_4158))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2521])).
% 4.50/1.81  tff(c_2634, plain, (![A_35, B_36, C_37, D_38, H_4158]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, H_4158)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(H_4158)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2575])).
% 4.50/1.81  tff(c_2638, plain, (![C_4218, H_4217, B_4220, D_4219, A_4216]: (k2_xboole_0(k2_enumset1(A_4216, B_4220, C_4218, D_4219), k1_tarski(H_4217))=k3_enumset1(A_4216, B_4220, C_4218, D_4219, H_4217))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2634])).
% 4.50/1.81  tff(c_2697, plain, (![A_32, B_33, C_34, H_4217]: (k3_enumset1(A_32, A_32, B_33, C_34, H_4217)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(H_4217)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2638])).
% 4.50/1.81  tff(c_2703, plain, (![A_4337, B_4338, C_4339, H_4340]: (k2_xboole_0(k1_enumset1(A_4337, B_4338, C_4339), k1_tarski(H_4340))=k2_enumset1(A_4337, B_4338, C_4339, H_4340))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2697])).
% 4.50/1.81  tff(c_2762, plain, (![A_30, B_31, H_4340]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(H_4340))=k2_enumset1(A_30, A_30, B_31, H_4340))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2703])).
% 4.50/1.81  tff(c_2766, plain, (![A_4397, B_4398, H_4399]: (k2_xboole_0(k2_tarski(A_4397, B_4398), k1_tarski(H_4399))=k1_enumset1(A_4397, B_4398, H_4399))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2762])).
% 4.50/1.81  tff(c_2831, plain, (![A_29, H_4399]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(H_4399))=k1_enumset1(A_29, A_29, H_4399))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2766])).
% 4.50/1.81  tff(c_2835, plain, (![A_4456, H_4457]: (k2_xboole_0(k1_tarski(A_4456), k1_tarski(H_4457))=k2_tarski(A_4456, H_4457))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2831])).
% 4.50/1.81  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.81  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.81  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.50/1.81  tff(c_192, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.81  tff(c_201, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_192])).
% 4.50/1.81  tff(c_204, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_201])).
% 4.50/1.81  tff(c_211, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.81  tff(c_220, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_211])).
% 4.50/1.81  tff(c_223, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_220])).
% 4.50/1.81  tff(c_2841, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2835, c_223])).
% 4.50/1.81  tff(c_149, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.50/1.81  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.50/1.81  tff(c_161, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_14])).
% 4.50/1.81  tff(c_2983, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2841, c_161])).
% 4.50/1.81  tff(c_36, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.50/1.81  tff(c_3027, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2983, c_36])).
% 4.50/1.81  tff(c_3070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3027])).
% 4.50/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.81  
% 4.50/1.81  Inference rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Ref     : 0
% 4.50/1.81  #Sup     : 428
% 4.50/1.81  #Fact    : 6
% 4.50/1.81  #Define  : 0
% 4.50/1.81  #Split   : 6
% 4.50/1.81  #Chain   : 0
% 4.50/1.81  #Close   : 0
% 4.50/1.81  
% 4.50/1.81  Ordering : KBO
% 4.50/1.81  
% 4.50/1.81  Simplification rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Subsume      : 51
% 4.50/1.82  #Demod        : 43
% 4.50/1.82  #Tautology    : 231
% 4.50/1.82  #SimpNegUnit  : 3
% 4.50/1.82  #BackRed      : 0
% 4.50/1.82  
% 4.50/1.82  #Partial instantiations: 1463
% 4.50/1.82  #Strategies tried      : 1
% 4.50/1.82  
% 4.50/1.82  Timing (in seconds)
% 4.50/1.82  ----------------------
% 4.50/1.82  Preprocessing        : 0.35
% 4.50/1.82  Parsing              : 0.18
% 4.50/1.82  CNF conversion       : 0.03
% 4.50/1.82  Main loop            : 0.69
% 4.50/1.82  Inferencing          : 0.32
% 4.50/1.82  Reduction            : 0.15
% 4.50/1.82  Demodulation         : 0.11
% 4.50/1.82  BG Simplification    : 0.04
% 4.50/1.82  Subsumption          : 0.15
% 4.50/1.82  Abstraction          : 0.04
% 4.50/1.82  MUC search           : 0.00
% 4.50/1.82  Cooper               : 0.00
% 4.50/1.82  Total                : 1.07
% 4.50/1.82  Index Insertion      : 0.00
% 4.50/1.82  Index Deletion       : 0.00
% 4.50/1.82  Index Matching       : 0.00
% 4.50/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
