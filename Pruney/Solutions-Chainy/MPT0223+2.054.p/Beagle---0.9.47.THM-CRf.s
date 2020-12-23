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
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   77 (  89 expanded)
%              Number of leaves         :   39 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :   61 (  74 expanded)
%              Number of equality atoms :   54 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_65,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [A_58] : k2_tarski(A_58,A_58) = k1_tarski(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,A_61,B_62,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [A_64,B_65,C_66,D_67] : k3_enumset1(A_64,A_64,B_65,C_66,D_67) = k2_enumset1(A_64,B_65,C_66,D_67) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ! [E_72,C_70,B_69,D_71,A_68] : k4_enumset1(A_68,A_68,B_69,C_70,D_71,E_72) = k3_enumset1(A_68,B_69,C_70,D_71,E_72) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,(
    ! [C_75,E_77,B_74,F_78,A_73,D_76] : k5_enumset1(A_73,A_73,B_74,C_75,D_76,E_77,F_78) = k4_enumset1(A_73,B_74,C_75,D_76,E_77,F_78) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    ! [E_83,F_84,C_81,G_85,B_80,A_79,D_82] : k6_enumset1(A_79,A_79,B_80,C_81,D_82,E_83,F_84,G_85) = k5_enumset1(A_79,B_80,C_81,D_82,E_83,F_84,G_85) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1850,plain,(
    ! [C_4336,E_4334,B_4338,G_4337,D_4340,A_4335,H_4341,F_4339] : k2_xboole_0(k5_enumset1(A_4335,B_4338,C_4336,D_4340,E_4334,F_4339,G_4337),k1_tarski(H_4341)) = k6_enumset1(A_4335,B_4338,C_4336,D_4340,E_4334,F_4339,G_4337,H_4341) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1859,plain,(
    ! [C_75,E_77,B_74,F_78,H_4341,A_73,D_76] : k6_enumset1(A_73,A_73,B_74,C_75,D_76,E_77,F_78,H_4341) = k2_xboole_0(k4_enumset1(A_73,B_74,C_75,D_76,E_77,F_78),k1_tarski(H_4341)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1850])).

tff(c_2004,plain,(
    ! [E_4619,D_4617,C_4616,A_4620,F_4615,H_4621,B_4618] : k2_xboole_0(k4_enumset1(A_4620,B_4618,C_4616,D_4617,E_4619,F_4615),k1_tarski(H_4621)) = k5_enumset1(A_4620,B_4618,C_4616,D_4617,E_4619,F_4615,H_4621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1859])).

tff(c_2013,plain,(
    ! [E_72,C_70,B_69,H_4621,D_71,A_68] : k5_enumset1(A_68,A_68,B_69,C_70,D_71,E_72,H_4621) = k2_xboole_0(k3_enumset1(A_68,B_69,C_70,D_71,E_72),k1_tarski(H_4621)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2004])).

tff(c_2069,plain,(
    ! [E_4691,H_4687,B_4690,A_4692,C_4689,D_4688] : k2_xboole_0(k3_enumset1(A_4692,B_4690,C_4689,D_4688,E_4691),k1_tarski(H_4687)) = k4_enumset1(A_4692,B_4690,C_4689,D_4688,E_4691,H_4687) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2013])).

tff(c_2078,plain,(
    ! [H_4687,D_67,C_66,A_64,B_65] : k4_enumset1(A_64,A_64,B_65,C_66,D_67,H_4687) = k2_xboole_0(k2_enumset1(A_64,B_65,C_66,D_67),k1_tarski(H_4687)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2069])).

tff(c_2199,plain,(
    ! [B_4833,D_4832,A_4836,H_4835,C_4834] : k2_xboole_0(k2_enumset1(A_4836,B_4833,C_4834,D_4832),k1_tarski(H_4835)) = k3_enumset1(A_4836,B_4833,C_4834,D_4832,H_4835) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2078])).

tff(c_2269,plain,(
    ! [A_61,B_62,C_63,H_4835] : k3_enumset1(A_61,A_61,B_62,C_63,H_4835) = k2_xboole_0(k1_enumset1(A_61,B_62,C_63),k1_tarski(H_4835)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2199])).

tff(c_2273,plain,(
    ! [A_4902,B_4903,C_4904,H_4905] : k2_xboole_0(k1_enumset1(A_4902,B_4903,C_4904),k1_tarski(H_4905)) = k2_enumset1(A_4902,B_4903,C_4904,H_4905) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2269])).

tff(c_2340,plain,(
    ! [A_59,B_60,H_4905] : k2_xboole_0(k2_tarski(A_59,B_60),k1_tarski(H_4905)) = k2_enumset1(A_59,A_59,B_60,H_4905) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2273])).

tff(c_2344,plain,(
    ! [A_4971,B_4972,H_4973] : k2_xboole_0(k2_tarski(A_4971,B_4972),k1_tarski(H_4973)) = k1_enumset1(A_4971,B_4972,H_4973) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2340])).

tff(c_2405,plain,(
    ! [A_58,H_4973] : k2_xboole_0(k1_tarski(A_58),k1_tarski(H_4973)) = k1_enumset1(A_58,A_58,H_4973) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2344])).

tff(c_2409,plain,(
    ! [A_5039,H_5040] : k2_xboole_0(k1_tarski(A_5039),k1_tarski(H_5040)) = k2_tarski(A_5039,H_5040) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2405])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_160])).

tff(c_172,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_179,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_176])).

tff(c_2415,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2409,c_179])).

tff(c_122,plain,(
    ! [A_101,B_102] : k1_enumset1(A_101,A_101,B_102) = k2_tarski(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    ! [B_102,A_101] : r2_hidden(B_102,k2_tarski(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_12])).

tff(c_2546,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2415,c_134])).

tff(c_34,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2610,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2546,c_34])).

tff(c_2654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:47:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.78  
% 4.38/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.79  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.38/1.79  
% 4.38/1.79  %Foreground sorts:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Background operators:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Foreground operators:
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.38/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.38/1.79  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.38/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.38/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.38/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.38/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.38/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.38/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.38/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.38/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.38/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.38/1.79  
% 4.38/1.80  tff(f_84, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.38/1.80  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.38/1.80  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.38/1.80  tff(f_71, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.38/1.80  tff(f_73, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.38/1.80  tff(f_75, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.38/1.80  tff(f_77, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.38/1.80  tff(f_79, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.38/1.80  tff(f_65, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 4.38/1.80  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.38/1.80  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.38/1.80  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.38/1.80  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.38/1.80  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.38/1.80  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.38/1.80  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.38/1.80  tff(c_58, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_56, plain, (![A_58]: (k2_tarski(A_58, A_58)=k1_tarski(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.38/1.80  tff(c_60, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, A_61, B_62, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.38/1.80  tff(c_62, plain, (![A_64, B_65, C_66, D_67]: (k3_enumset1(A_64, A_64, B_65, C_66, D_67)=k2_enumset1(A_64, B_65, C_66, D_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.38/1.80  tff(c_64, plain, (![E_72, C_70, B_69, D_71, A_68]: (k4_enumset1(A_68, A_68, B_69, C_70, D_71, E_72)=k3_enumset1(A_68, B_69, C_70, D_71, E_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.38/1.80  tff(c_66, plain, (![C_75, E_77, B_74, F_78, A_73, D_76]: (k5_enumset1(A_73, A_73, B_74, C_75, D_76, E_77, F_78)=k4_enumset1(A_73, B_74, C_75, D_76, E_77, F_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.38/1.80  tff(c_68, plain, (![E_83, F_84, C_81, G_85, B_80, A_79, D_82]: (k6_enumset1(A_79, A_79, B_80, C_81, D_82, E_83, F_84, G_85)=k5_enumset1(A_79, B_80, C_81, D_82, E_83, F_84, G_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.38/1.80  tff(c_1850, plain, (![C_4336, E_4334, B_4338, G_4337, D_4340, A_4335, H_4341, F_4339]: (k2_xboole_0(k5_enumset1(A_4335, B_4338, C_4336, D_4340, E_4334, F_4339, G_4337), k1_tarski(H_4341))=k6_enumset1(A_4335, B_4338, C_4336, D_4340, E_4334, F_4339, G_4337, H_4341))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.38/1.80  tff(c_1859, plain, (![C_75, E_77, B_74, F_78, H_4341, A_73, D_76]: (k6_enumset1(A_73, A_73, B_74, C_75, D_76, E_77, F_78, H_4341)=k2_xboole_0(k4_enumset1(A_73, B_74, C_75, D_76, E_77, F_78), k1_tarski(H_4341)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1850])).
% 4.38/1.80  tff(c_2004, plain, (![E_4619, D_4617, C_4616, A_4620, F_4615, H_4621, B_4618]: (k2_xboole_0(k4_enumset1(A_4620, B_4618, C_4616, D_4617, E_4619, F_4615), k1_tarski(H_4621))=k5_enumset1(A_4620, B_4618, C_4616, D_4617, E_4619, F_4615, H_4621))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1859])).
% 4.38/1.80  tff(c_2013, plain, (![E_72, C_70, B_69, H_4621, D_71, A_68]: (k5_enumset1(A_68, A_68, B_69, C_70, D_71, E_72, H_4621)=k2_xboole_0(k3_enumset1(A_68, B_69, C_70, D_71, E_72), k1_tarski(H_4621)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2004])).
% 4.38/1.80  tff(c_2069, plain, (![E_4691, H_4687, B_4690, A_4692, C_4689, D_4688]: (k2_xboole_0(k3_enumset1(A_4692, B_4690, C_4689, D_4688, E_4691), k1_tarski(H_4687))=k4_enumset1(A_4692, B_4690, C_4689, D_4688, E_4691, H_4687))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2013])).
% 4.38/1.80  tff(c_2078, plain, (![H_4687, D_67, C_66, A_64, B_65]: (k4_enumset1(A_64, A_64, B_65, C_66, D_67, H_4687)=k2_xboole_0(k2_enumset1(A_64, B_65, C_66, D_67), k1_tarski(H_4687)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2069])).
% 4.38/1.80  tff(c_2199, plain, (![B_4833, D_4832, A_4836, H_4835, C_4834]: (k2_xboole_0(k2_enumset1(A_4836, B_4833, C_4834, D_4832), k1_tarski(H_4835))=k3_enumset1(A_4836, B_4833, C_4834, D_4832, H_4835))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2078])).
% 4.38/1.80  tff(c_2269, plain, (![A_61, B_62, C_63, H_4835]: (k3_enumset1(A_61, A_61, B_62, C_63, H_4835)=k2_xboole_0(k1_enumset1(A_61, B_62, C_63), k1_tarski(H_4835)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2199])).
% 4.38/1.80  tff(c_2273, plain, (![A_4902, B_4903, C_4904, H_4905]: (k2_xboole_0(k1_enumset1(A_4902, B_4903, C_4904), k1_tarski(H_4905))=k2_enumset1(A_4902, B_4903, C_4904, H_4905))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2269])).
% 4.38/1.80  tff(c_2340, plain, (![A_59, B_60, H_4905]: (k2_xboole_0(k2_tarski(A_59, B_60), k1_tarski(H_4905))=k2_enumset1(A_59, A_59, B_60, H_4905))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2273])).
% 4.38/1.80  tff(c_2344, plain, (![A_4971, B_4972, H_4973]: (k2_xboole_0(k2_tarski(A_4971, B_4972), k1_tarski(H_4973))=k1_enumset1(A_4971, B_4972, H_4973))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2340])).
% 4.38/1.80  tff(c_2405, plain, (![A_58, H_4973]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(H_4973))=k1_enumset1(A_58, A_58, H_4973))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2344])).
% 4.38/1.80  tff(c_2409, plain, (![A_5039, H_5040]: (k2_xboole_0(k1_tarski(A_5039), k1_tarski(H_5040))=k2_tarski(A_5039, H_5040))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2405])).
% 4.38/1.80  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.38/1.80  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.80  tff(c_72, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.38/1.80  tff(c_160, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.80  tff(c_169, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_160])).
% 4.38/1.80  tff(c_172, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_169])).
% 4.38/1.80  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.80  tff(c_176, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 4.38/1.80  tff(c_179, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_176])).
% 4.38/1.80  tff(c_2415, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2409, c_179])).
% 4.38/1.80  tff(c_122, plain, (![A_101, B_102]: (k1_enumset1(A_101, A_101, B_102)=k2_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_12, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.38/1.80  tff(c_134, plain, (![B_102, A_101]: (r2_hidden(B_102, k2_tarski(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_12])).
% 4.38/1.80  tff(c_2546, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2415, c_134])).
% 4.38/1.80  tff(c_34, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.38/1.80  tff(c_2610, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2546, c_34])).
% 4.38/1.80  tff(c_2654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2610])).
% 4.38/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.80  
% 4.38/1.80  Inference rules
% 4.38/1.80  ----------------------
% 4.38/1.80  #Ref     : 0
% 4.38/1.80  #Sup     : 340
% 4.38/1.80  #Fact    : 0
% 4.38/1.80  #Define  : 0
% 4.38/1.80  #Split   : 6
% 4.38/1.80  #Chain   : 0
% 4.38/1.80  #Close   : 0
% 4.38/1.80  
% 4.38/1.80  Ordering : KBO
% 4.38/1.80  
% 4.38/1.80  Simplification rules
% 4.38/1.80  ----------------------
% 4.38/1.80  #Subsume      : 51
% 4.38/1.80  #Demod        : 56
% 4.38/1.80  #Tautology    : 142
% 4.38/1.80  #SimpNegUnit  : 1
% 4.38/1.80  #BackRed      : 0
% 4.38/1.80  
% 4.38/1.80  #Partial instantiations: 1520
% 4.38/1.80  #Strategies tried      : 1
% 4.38/1.80  
% 4.38/1.80  Timing (in seconds)
% 4.38/1.80  ----------------------
% 4.38/1.80  Preprocessing        : 0.37
% 4.38/1.80  Parsing              : 0.19
% 4.38/1.80  CNF conversion       : 0.03
% 4.38/1.80  Main loop            : 0.68
% 4.38/1.81  Inferencing          : 0.34
% 4.38/1.81  Reduction            : 0.16
% 4.38/1.81  Demodulation         : 0.12
% 4.38/1.81  BG Simplification    : 0.04
% 4.38/1.81  Subsumption          : 0.11
% 4.38/1.81  Abstraction          : 0.03
% 4.38/1.81  MUC search           : 0.00
% 4.38/1.81  Cooper               : 0.00
% 4.38/1.81  Total                : 1.08
% 4.38/1.81  Index Insertion      : 0.00
% 4.38/1.81  Index Deletion       : 0.00
% 4.38/1.81  Index Matching       : 0.00
% 4.38/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
