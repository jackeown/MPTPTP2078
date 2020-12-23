%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:18 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

tff(c_2074,plain,(
    ! [D_3618,G_3616,C_3620,B_3622,H_3619,E_3623,A_3617,F_3621] : k2_xboole_0(k5_enumset1(A_3617,B_3622,C_3620,D_3618,E_3623,F_3621,G_3616),k1_tarski(H_3619)) = k6_enumset1(A_3617,B_3622,C_3620,D_3618,E_3623,F_3621,G_3616,H_3619) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2089,plain,(
    ! [C_46,E_48,F_49,A_44,H_3619,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,H_3619) = k2_xboole_0(k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49),k1_tarski(H_3619)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2074])).

tff(c_2152,plain,(
    ! [A_3686,B_3685,E_3680,D_3682,C_3683,H_3684,F_3681] : k2_xboole_0(k4_enumset1(A_3686,B_3685,C_3683,D_3682,E_3680,F_3681),k1_tarski(H_3684)) = k5_enumset1(A_3686,B_3685,C_3683,D_3682,E_3680,F_3681,H_3684) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2089])).

tff(c_2167,plain,(
    ! [E_43,D_42,A_39,C_41,B_40,H_3684] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,H_3684) = k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k1_tarski(H_3684)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2152])).

tff(c_2230,plain,(
    ! [D_3746,C_3745,B_3744,E_3748,A_3743,H_3747] : k2_xboole_0(k3_enumset1(A_3743,B_3744,C_3745,D_3746,E_3748),k1_tarski(H_3747)) = k4_enumset1(A_3743,B_3744,C_3745,D_3746,E_3748,H_3747) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2167])).

tff(c_2245,plain,(
    ! [A_35,B_36,C_37,D_38,H_3747] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,H_3747) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(H_3747)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2230])).

tff(c_2308,plain,(
    ! [H_3807,C_3806,B_3809,D_3808,A_3805] : k2_xboole_0(k2_enumset1(A_3805,B_3809,C_3806,D_3808),k1_tarski(H_3807)) = k3_enumset1(A_3805,B_3809,C_3806,D_3808,H_3807) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2245])).

tff(c_2373,plain,(
    ! [A_32,B_33,C_34,H_3807] : k3_enumset1(A_32,A_32,B_33,C_34,H_3807) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(H_3807)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2308])).

tff(c_2388,plain,(
    ! [A_3926,B_3927,C_3928,H_3929] : k2_xboole_0(k1_enumset1(A_3926,B_3927,C_3928),k1_tarski(H_3929)) = k2_enumset1(A_3926,B_3927,C_3928,H_3929) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2373])).

tff(c_2453,plain,(
    ! [A_30,B_31,H_3929] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(H_3929)) = k2_enumset1(A_30,A_30,B_31,H_3929) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2388])).

tff(c_2466,plain,(
    ! [A_3986,B_3987,H_3988] : k2_xboole_0(k2_tarski(A_3986,B_3987),k1_tarski(H_3988)) = k1_enumset1(A_3986,B_3987,H_3988) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2453])).

tff(c_2537,plain,(
    ! [A_29,H_3988] : k2_xboole_0(k1_tarski(A_29),k1_tarski(H_3988)) = k1_enumset1(A_29,A_29,H_3988) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2466])).

tff(c_2544,plain,(
    ! [A_4045,H_4046] : k2_xboole_0(k1_tarski(A_4045),k1_tarski(H_4046)) = k2_tarski(A_4045,H_4046) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2537])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_178])).

tff(c_190,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_187])).

tff(c_195,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_195])).

tff(c_207,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_204])).

tff(c_2550,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2544,c_207])).

tff(c_149,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_161,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_14])).

tff(c_2692,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2550,c_161])).

tff(c_36,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2732,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2692,c_36])).

tff(c_2775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.91  
% 4.52/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.92  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.52/1.92  
% 4.52/1.92  %Foreground sorts:
% 4.52/1.92  
% 4.52/1.92  
% 4.52/1.92  %Background operators:
% 4.52/1.92  
% 4.52/1.92  
% 4.52/1.92  %Foreground operators:
% 4.52/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.52/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.52/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.52/1.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.52/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.52/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.52/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.52/1.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.52/1.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.52/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.52/1.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.52/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.52/1.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.52/1.92  
% 4.52/1.93  tff(f_78, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.52/1.93  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.52/1.93  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.52/1.93  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.52/1.93  tff(f_67, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.52/1.93  tff(f_69, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.52/1.93  tff(f_71, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.52/1.93  tff(f_73, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.52/1.93  tff(f_59, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 4.52/1.93  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.52/1.93  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.52/1.93  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.52/1.93  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.52/1.93  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.52/1.93  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.52/1.93  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.52/1.93  tff(c_52, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.52/1.93  tff(c_50, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.52/1.93  tff(c_54, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.52/1.93  tff(c_56, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.52/1.93  tff(c_58, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.52/1.93  tff(c_60, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.93  tff(c_62, plain, (![A_50, B_51, G_56, E_54, C_52, D_53, F_55]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56)=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.52/1.93  tff(c_2074, plain, (![D_3618, G_3616, C_3620, B_3622, H_3619, E_3623, A_3617, F_3621]: (k2_xboole_0(k5_enumset1(A_3617, B_3622, C_3620, D_3618, E_3623, F_3621, G_3616), k1_tarski(H_3619))=k6_enumset1(A_3617, B_3622, C_3620, D_3618, E_3623, F_3621, G_3616, H_3619))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.52/1.93  tff(c_2089, plain, (![C_46, E_48, F_49, A_44, H_3619, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, H_3619)=k2_xboole_0(k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49), k1_tarski(H_3619)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2074])).
% 4.52/1.93  tff(c_2152, plain, (![A_3686, B_3685, E_3680, D_3682, C_3683, H_3684, F_3681]: (k2_xboole_0(k4_enumset1(A_3686, B_3685, C_3683, D_3682, E_3680, F_3681), k1_tarski(H_3684))=k5_enumset1(A_3686, B_3685, C_3683, D_3682, E_3680, F_3681, H_3684))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2089])).
% 4.52/1.93  tff(c_2167, plain, (![E_43, D_42, A_39, C_41, B_40, H_3684]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, H_3684)=k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k1_tarski(H_3684)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2152])).
% 4.52/1.93  tff(c_2230, plain, (![D_3746, C_3745, B_3744, E_3748, A_3743, H_3747]: (k2_xboole_0(k3_enumset1(A_3743, B_3744, C_3745, D_3746, E_3748), k1_tarski(H_3747))=k4_enumset1(A_3743, B_3744, C_3745, D_3746, E_3748, H_3747))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2167])).
% 4.52/1.93  tff(c_2245, plain, (![A_35, B_36, C_37, D_38, H_3747]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, H_3747)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(H_3747)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2230])).
% 4.52/1.93  tff(c_2308, plain, (![H_3807, C_3806, B_3809, D_3808, A_3805]: (k2_xboole_0(k2_enumset1(A_3805, B_3809, C_3806, D_3808), k1_tarski(H_3807))=k3_enumset1(A_3805, B_3809, C_3806, D_3808, H_3807))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2245])).
% 4.52/1.93  tff(c_2373, plain, (![A_32, B_33, C_34, H_3807]: (k3_enumset1(A_32, A_32, B_33, C_34, H_3807)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(H_3807)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2308])).
% 4.52/1.93  tff(c_2388, plain, (![A_3926, B_3927, C_3928, H_3929]: (k2_xboole_0(k1_enumset1(A_3926, B_3927, C_3928), k1_tarski(H_3929))=k2_enumset1(A_3926, B_3927, C_3928, H_3929))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2373])).
% 4.52/1.93  tff(c_2453, plain, (![A_30, B_31, H_3929]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(H_3929))=k2_enumset1(A_30, A_30, B_31, H_3929))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2388])).
% 4.52/1.93  tff(c_2466, plain, (![A_3986, B_3987, H_3988]: (k2_xboole_0(k2_tarski(A_3986, B_3987), k1_tarski(H_3988))=k1_enumset1(A_3986, B_3987, H_3988))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2453])).
% 4.52/1.93  tff(c_2537, plain, (![A_29, H_3988]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(H_3988))=k1_enumset1(A_29, A_29, H_3988))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2466])).
% 4.52/1.93  tff(c_2544, plain, (![A_4045, H_4046]: (k2_xboole_0(k1_tarski(A_4045), k1_tarski(H_4046))=k2_tarski(A_4045, H_4046))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2537])).
% 4.52/1.93  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.93  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.93  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.52/1.93  tff(c_178, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.52/1.93  tff(c_187, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_178])).
% 4.52/1.93  tff(c_190, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_187])).
% 4.52/1.93  tff(c_195, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.93  tff(c_204, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_195])).
% 4.52/1.93  tff(c_207, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_204])).
% 4.52/1.93  tff(c_2550, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2544, c_207])).
% 4.52/1.93  tff(c_149, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.52/1.93  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.93  tff(c_161, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_14])).
% 4.52/1.93  tff(c_2692, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2550, c_161])).
% 4.52/1.93  tff(c_36, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.52/1.93  tff(c_2732, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2692, c_36])).
% 4.52/1.93  tff(c_2775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2732])).
% 4.52/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.93  
% 4.52/1.93  Inference rules
% 4.52/1.93  ----------------------
% 4.52/1.93  #Ref     : 0
% 4.52/1.93  #Sup     : 376
% 4.52/1.93  #Fact    : 6
% 4.52/1.93  #Define  : 0
% 4.52/1.93  #Split   : 6
% 4.52/1.93  #Chain   : 0
% 4.52/1.93  #Close   : 0
% 4.52/1.93  
% 4.52/1.93  Ordering : KBO
% 4.52/1.93  
% 4.52/1.93  Simplification rules
% 4.52/1.93  ----------------------
% 4.52/1.93  #Subsume      : 31
% 4.52/1.93  #Demod        : 51
% 4.52/1.93  #Tautology    : 192
% 4.52/1.93  #SimpNegUnit  : 3
% 4.52/1.93  #BackRed      : 0
% 4.52/1.93  
% 4.52/1.93  #Partial instantiations: 1330
% 4.52/1.93  #Strategies tried      : 1
% 4.52/1.93  
% 4.52/1.93  Timing (in seconds)
% 4.52/1.93  ----------------------
% 4.52/1.94  Preprocessing        : 0.37
% 4.52/1.94  Parsing              : 0.19
% 4.52/1.94  CNF conversion       : 0.03
% 4.52/1.94  Main loop            : 0.74
% 4.52/1.94  Inferencing          : 0.35
% 4.52/1.94  Reduction            : 0.17
% 4.52/1.94  Demodulation         : 0.12
% 4.52/1.94  BG Simplification    : 0.04
% 4.52/1.94  Subsumption          : 0.14
% 4.52/1.94  Abstraction          : 0.04
% 4.52/1.94  MUC search           : 0.00
% 4.52/1.94  Cooper               : 0.00
% 4.52/1.94  Total                : 1.14
% 4.52/1.94  Index Insertion      : 0.00
% 4.52/1.94  Index Deletion       : 0.00
% 4.52/1.94  Index Matching       : 0.00
% 4.52/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
