%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
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

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
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
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [D_48,C_47,A_45,B_46,E_49,F_50] : k5_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50) = k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [G_57,B_52,E_55,F_56,C_53,D_54,A_51] : k6_enumset1(A_51,A_51,B_52,C_53,D_54,E_55,F_56,G_57) = k5_enumset1(A_51,B_52,C_53,D_54,E_55,F_56,G_57) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2074,plain,(
    ! [A_3860,B_3867,F_3863,C_3861,E_3862,H_3865,G_3864,D_3866] : k2_xboole_0(k5_enumset1(A_3860,B_3867,C_3861,D_3866,E_3862,F_3863,G_3864),k1_tarski(H_3865)) = k6_enumset1(A_3860,B_3867,C_3861,D_3866,E_3862,F_3863,G_3864,H_3865) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2083,plain,(
    ! [D_48,C_47,A_45,B_46,H_3865,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,H_3865) = k2_xboole_0(k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50),k1_tarski(H_3865)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2074])).

tff(c_2842,plain,(
    ! [C_4397,E_4398,B_4394,A_4395,H_4399,D_4396,F_4400] : k2_xboole_0(k4_enumset1(A_4395,B_4394,C_4397,D_4396,E_4398,F_4400),k1_tarski(H_4399)) = k5_enumset1(A_4395,B_4394,C_4397,D_4396,E_4398,F_4400,H_4399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2083])).

tff(c_2851,plain,(
    ! [E_44,C_42,H_4399,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,H_4399) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_tarski(H_4399)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2842])).

tff(c_2907,plain,(
    ! [B_4522,D_4519,A_4518,C_4520,E_4517,H_4521] : k2_xboole_0(k3_enumset1(A_4518,B_4522,C_4520,D_4519,E_4517),k1_tarski(H_4521)) = k4_enumset1(A_4518,B_4522,C_4520,D_4519,E_4517,H_4521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2851])).

tff(c_2966,plain,(
    ! [D_39,A_36,H_4521,C_38,B_37] : k4_enumset1(A_36,A_36,B_37,C_38,D_39,H_4521) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),k1_tarski(H_4521)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2907])).

tff(c_2970,plain,(
    ! [B_4582,H_4579,D_4581,C_4583,A_4580] : k2_xboole_0(k2_enumset1(A_4580,B_4582,C_4583,D_4581),k1_tarski(H_4579)) = k3_enumset1(A_4580,B_4582,C_4583,D_4581,H_4579) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2966])).

tff(c_3029,plain,(
    ! [A_33,B_34,C_35,H_4579] : k3_enumset1(A_33,A_33,B_34,C_35,H_4579) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),k1_tarski(H_4579)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2970])).

tff(c_3033,plain,(
    ! [A_4640,B_4641,C_4642,H_4643] : k2_xboole_0(k1_enumset1(A_4640,B_4641,C_4642),k1_tarski(H_4643)) = k2_enumset1(A_4640,B_4641,C_4642,H_4643) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3029])).

tff(c_3101,plain,(
    ! [A_31,B_32,H_4643] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(H_4643)) = k2_enumset1(A_31,A_31,B_32,H_4643) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3033])).

tff(c_3139,plain,(
    ! [A_4760,B_4761,H_4762] : k2_xboole_0(k2_tarski(A_4760,B_4761),k1_tarski(H_4762)) = k1_enumset1(A_4760,B_4761,H_4762) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3101])).

tff(c_3198,plain,(
    ! [A_30,H_4762] : k2_xboole_0(k1_tarski(A_30),k1_tarski(H_4762)) = k1_enumset1(A_30,A_30,H_4762) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3139])).

tff(c_3202,plain,(
    ! [A_4819,H_4820] : k2_xboole_0(k1_tarski(A_4819),k1_tarski(H_4820)) = k2_tarski(A_4819,H_4820) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3198])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_145,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_145])).

tff(c_157,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_154])).

tff(c_283,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_292,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_283])).

tff(c_295,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_292])).

tff(c_3208,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3202,c_295])).

tff(c_116,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [B_74,A_73] : r2_hidden(B_74,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_12])).

tff(c_3338,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3208,c_128])).

tff(c_34,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3378,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3338,c_34])).

tff(c_3421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.93  
% 4.92/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.92/1.94  
% 4.92/1.94  %Foreground sorts:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Background operators:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Foreground operators:
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.92/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.92/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.92/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.92/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.92/1.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.92/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.92/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.92/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.92/1.94  tff('#skF_6', type, '#skF_6': $i).
% 4.92/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.92/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.92/1.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.92/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.92/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.92/1.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.92/1.94  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.92/1.94  
% 4.92/1.95  tff(f_78, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.92/1.95  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.92/1.95  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.92/1.95  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.92/1.95  tff(f_67, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.92/1.95  tff(f_69, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.92/1.95  tff(f_71, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.92/1.95  tff(f_73, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.92/1.95  tff(f_59, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 4.92/1.95  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.92/1.95  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.92/1.95  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.92/1.95  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.92/1.95  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.92/1.95  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.92/1.95  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.92/1.95  tff(c_52, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.92/1.95  tff(c_50, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.92/1.95  tff(c_54, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.92/1.95  tff(c_56, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.92/1.95  tff(c_58, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.92/1.95  tff(c_60, plain, (![D_48, C_47, A_45, B_46, E_49, F_50]: (k5_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50)=k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.92/1.95  tff(c_62, plain, (![G_57, B_52, E_55, F_56, C_53, D_54, A_51]: (k6_enumset1(A_51, A_51, B_52, C_53, D_54, E_55, F_56, G_57)=k5_enumset1(A_51, B_52, C_53, D_54, E_55, F_56, G_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.92/1.95  tff(c_2074, plain, (![A_3860, B_3867, F_3863, C_3861, E_3862, H_3865, G_3864, D_3866]: (k2_xboole_0(k5_enumset1(A_3860, B_3867, C_3861, D_3866, E_3862, F_3863, G_3864), k1_tarski(H_3865))=k6_enumset1(A_3860, B_3867, C_3861, D_3866, E_3862, F_3863, G_3864, H_3865))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.92/1.95  tff(c_2083, plain, (![D_48, C_47, A_45, B_46, H_3865, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, H_3865)=k2_xboole_0(k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50), k1_tarski(H_3865)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2074])).
% 4.92/1.95  tff(c_2842, plain, (![C_4397, E_4398, B_4394, A_4395, H_4399, D_4396, F_4400]: (k2_xboole_0(k4_enumset1(A_4395, B_4394, C_4397, D_4396, E_4398, F_4400), k1_tarski(H_4399))=k5_enumset1(A_4395, B_4394, C_4397, D_4396, E_4398, F_4400, H_4399))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2083])).
% 4.92/1.95  tff(c_2851, plain, (![E_44, C_42, H_4399, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, H_4399)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_tarski(H_4399)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2842])).
% 4.92/1.95  tff(c_2907, plain, (![B_4522, D_4519, A_4518, C_4520, E_4517, H_4521]: (k2_xboole_0(k3_enumset1(A_4518, B_4522, C_4520, D_4519, E_4517), k1_tarski(H_4521))=k4_enumset1(A_4518, B_4522, C_4520, D_4519, E_4517, H_4521))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2851])).
% 4.92/1.95  tff(c_2966, plain, (![D_39, A_36, H_4521, C_38, B_37]: (k4_enumset1(A_36, A_36, B_37, C_38, D_39, H_4521)=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), k1_tarski(H_4521)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2907])).
% 4.92/1.95  tff(c_2970, plain, (![B_4582, H_4579, D_4581, C_4583, A_4580]: (k2_xboole_0(k2_enumset1(A_4580, B_4582, C_4583, D_4581), k1_tarski(H_4579))=k3_enumset1(A_4580, B_4582, C_4583, D_4581, H_4579))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2966])).
% 4.92/1.95  tff(c_3029, plain, (![A_33, B_34, C_35, H_4579]: (k3_enumset1(A_33, A_33, B_34, C_35, H_4579)=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), k1_tarski(H_4579)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2970])).
% 4.92/1.95  tff(c_3033, plain, (![A_4640, B_4641, C_4642, H_4643]: (k2_xboole_0(k1_enumset1(A_4640, B_4641, C_4642), k1_tarski(H_4643))=k2_enumset1(A_4640, B_4641, C_4642, H_4643))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3029])).
% 4.92/1.95  tff(c_3101, plain, (![A_31, B_32, H_4643]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(H_4643))=k2_enumset1(A_31, A_31, B_32, H_4643))), inference(superposition, [status(thm), theory('equality')], [c_52, c_3033])).
% 4.92/1.95  tff(c_3139, plain, (![A_4760, B_4761, H_4762]: (k2_xboole_0(k2_tarski(A_4760, B_4761), k1_tarski(H_4762))=k1_enumset1(A_4760, B_4761, H_4762))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3101])).
% 4.92/1.95  tff(c_3198, plain, (![A_30, H_4762]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(H_4762))=k1_enumset1(A_30, A_30, H_4762))), inference(superposition, [status(thm), theory('equality')], [c_50, c_3139])).
% 4.92/1.95  tff(c_3202, plain, (![A_4819, H_4820]: (k2_xboole_0(k1_tarski(A_4819), k1_tarski(H_4820))=k2_tarski(A_4819, H_4820))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3198])).
% 4.92/1.95  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.92/1.95  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.95  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.92/1.95  tff(c_145, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.92/1.95  tff(c_154, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_145])).
% 4.92/1.95  tff(c_157, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_154])).
% 4.92/1.95  tff(c_283, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k4_xboole_0(B_87, A_86))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.92/1.95  tff(c_292, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_283])).
% 4.92/1.95  tff(c_295, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_292])).
% 4.92/1.95  tff(c_3208, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3202, c_295])).
% 4.92/1.95  tff(c_116, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.92/1.95  tff(c_12, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.92/1.95  tff(c_128, plain, (![B_74, A_73]: (r2_hidden(B_74, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_12])).
% 4.92/1.95  tff(c_3338, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3208, c_128])).
% 4.92/1.95  tff(c_34, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.92/1.95  tff(c_3378, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_3338, c_34])).
% 4.92/1.95  tff(c_3421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3378])).
% 4.92/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.95  
% 4.92/1.95  Inference rules
% 4.92/1.95  ----------------------
% 4.92/1.95  #Ref     : 0
% 4.92/1.95  #Sup     : 506
% 4.92/1.95  #Fact    : 6
% 4.92/1.95  #Define  : 0
% 4.92/1.95  #Split   : 6
% 4.92/1.95  #Chain   : 0
% 4.92/1.95  #Close   : 0
% 4.92/1.95  
% 4.92/1.95  Ordering : KBO
% 4.92/1.95  
% 4.92/1.95  Simplification rules
% 4.92/1.95  ----------------------
% 4.92/1.95  #Subsume      : 74
% 4.92/1.95  #Demod        : 65
% 4.92/1.95  #Tautology    : 271
% 4.92/1.95  #SimpNegUnit  : 3
% 4.92/1.95  #BackRed      : 0
% 4.92/1.95  
% 4.92/1.95  #Partial instantiations: 1577
% 4.92/1.95  #Strategies tried      : 1
% 4.92/1.95  
% 4.92/1.95  Timing (in seconds)
% 4.92/1.95  ----------------------
% 4.92/1.96  Preprocessing        : 0.35
% 4.92/1.96  Parsing              : 0.17
% 4.92/1.96  CNF conversion       : 0.03
% 4.92/1.96  Main loop            : 0.83
% 4.92/1.96  Inferencing          : 0.38
% 4.92/1.96  Reduction            : 0.20
% 4.92/1.96  Demodulation         : 0.15
% 4.92/1.96  BG Simplification    : 0.05
% 4.92/1.96  Subsumption          : 0.16
% 4.92/1.96  Abstraction          : 0.05
% 4.92/1.96  MUC search           : 0.00
% 4.92/1.96  Cooper               : 0.00
% 4.92/1.96  Total                : 1.22
% 4.92/1.96  Index Insertion      : 0.00
% 4.92/1.96  Index Deletion       : 0.00
% 4.92/1.96  Index Matching       : 0.00
% 4.92/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
