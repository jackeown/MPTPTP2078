%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 136 expanded)
%              Number of leaves         :   41 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 180 expanded)
%              Number of equality atoms :   43 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_103,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_95,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_76,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [A_27] : r1_tarski(k1_xboole_0,A_27) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_195,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,(
    ! [A_27] : k3_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_195])).

tff(c_579,plain,(
    ! [D_125,B_126,A_127] :
      ( r2_hidden(D_125,B_126)
      | ~ r2_hidden(D_125,k3_xboole_0(A_127,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_601,plain,(
    ! [D_128,A_129] :
      ( r2_hidden(D_128,A_129)
      | ~ r2_hidden(D_128,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_579])).

tff(c_613,plain,(
    ! [A_129] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_129)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_601])).

tff(c_614,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_532,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_4'(A_114,B_115),A_114)
      | r1_xboole_0(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_545,plain,(
    ! [A_116,B_117] :
      ( ~ v1_xboole_0(A_116)
      | r1_xboole_0(A_116,B_117) ) ),
    inference(resolution,[status(thm)],[c_532,c_4])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_551,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = A_116
      | ~ v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_545,c_52])).

tff(c_619,plain,(
    ! [B_117] : k4_xboole_0(k1_xboole_0,B_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_614,c_551])).

tff(c_56,plain,(
    ! [B_35,A_34] : k2_tarski(B_35,A_34) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_159,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_238,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_159])).

tff(c_66,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_265,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_66])).

tff(c_281,plain,(
    ! [A_81] : k2_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_42])).

tff(c_650,plain,(
    ! [A_133,B_134] : k4_xboole_0(k2_xboole_0(A_133,B_134),B_134) = k4_xboole_0(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_673,plain,(
    ! [A_81] : k4_xboole_0(k1_xboole_0,A_81) = k4_xboole_0(A_81,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_650])).

tff(c_691,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_673])).

tff(c_38,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_202,plain,(
    ! [B_21] : k3_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_765,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k3_xboole_0(A_138,B_139)) = k4_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_777,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_765])).

tff(c_781,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_777])).

tff(c_58,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1069,plain,(
    ! [A_161,B_162,C_163] :
      ( r1_tarski(k2_tarski(A_161,B_162),C_163)
      | ~ r2_hidden(B_162,C_163)
      | ~ r2_hidden(A_161,C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4605,plain,(
    ! [A_298,C_299] :
      ( r1_tarski(k1_tarski(A_298),C_299)
      | ~ r2_hidden(A_298,C_299)
      | ~ r2_hidden(A_298,C_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1069])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6070,plain,(
    ! [A_343,C_344] :
      ( k3_xboole_0(k1_tarski(A_343),C_344) = k1_tarski(A_343)
      | ~ r2_hidden(A_343,C_344) ) ),
    inference(resolution,[status(thm)],[c_4605,c_44])).

tff(c_40,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6141,plain,(
    ! [A_343,C_344] :
      ( k5_xboole_0(k1_tarski(A_343),k1_tarski(A_343)) = k4_xboole_0(k1_tarski(A_343),C_344)
      | ~ r2_hidden(A_343,C_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6070,c_40])).

tff(c_6579,plain,(
    ! [A_365,C_366] :
      ( k4_xboole_0(k1_tarski(A_365),C_366) = k1_xboole_0
      | ~ r2_hidden(A_365,C_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_6141])).

tff(c_48,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6668,plain,(
    ! [C_366,A_365] :
      ( k2_xboole_0(C_366,k1_tarski(A_365)) = k2_xboole_0(C_366,k1_xboole_0)
      | ~ r2_hidden(A_365,C_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6579,c_48])).

tff(c_6751,plain,(
    ! [C_367,A_368] :
      ( k2_xboole_0(C_367,k1_tarski(A_368)) = C_367
      | ~ r2_hidden(A_368,C_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6668])).

tff(c_244,plain,(
    ! [B_79,A_78] : k2_xboole_0(B_79,A_78) = k2_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_66])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_264,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_74])).

tff(c_6841,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6751,c_264])).

tff(c_6914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6841])).

tff(c_6917,plain,(
    ! [A_369] : r2_hidden('#skF_1'(k1_xboole_0),A_369) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_6946,plain,(
    ! [A_369] : ~ v1_xboole_0(A_369) ),
    inference(resolution,[status(thm)],[c_6917,c_4])).

tff(c_109,plain,(
    ! [B_60,A_61] :
      ( ~ r2_hidden(B_60,A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_114,plain,(
    ! [A_3] :
      ( ~ r2_hidden(A_3,'#skF_1'(A_3))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_6944,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6917,c_114])).

tff(c_6950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6946,c_6944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:18:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.13/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.39  
% 6.13/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.13/2.39  
% 6.13/2.39  %Foreground sorts:
% 6.13/2.39  
% 6.13/2.39  
% 6.13/2.39  %Background operators:
% 6.13/2.39  
% 6.13/2.39  
% 6.13/2.39  %Foreground operators:
% 6.13/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.13/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.13/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.13/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.13/2.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.13/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.13/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.13/2.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.13/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.13/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.13/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.13/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.13/2.39  tff('#skF_6', type, '#skF_6': $i).
% 6.13/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.13/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.13/2.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.13/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.13/2.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.13/2.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.13/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.13/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.13/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.13/2.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.13/2.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.13/2.39  
% 6.13/2.41  tff(f_114, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 6.13/2.41  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.13/2.41  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.13/2.41  tff(f_83, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.13/2.41  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.13/2.41  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.13/2.41  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.13/2.41  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.13/2.41  tff(f_93, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.13/2.41  tff(f_103, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.13/2.41  tff(f_87, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.13/2.41  tff(f_73, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.13/2.41  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.13/2.41  tff(f_95, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.13/2.41  tff(f_109, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.13/2.41  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.13/2.41  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.13/2.41  tff(c_76, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.41  tff(c_42, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.13/2.41  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.13/2.41  tff(c_46, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.13/2.41  tff(c_195, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.13/2.41  tff(c_203, plain, (![A_27]: (k3_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_195])).
% 6.13/2.41  tff(c_579, plain, (![D_125, B_126, A_127]: (r2_hidden(D_125, B_126) | ~r2_hidden(D_125, k3_xboole_0(A_127, B_126)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.13/2.41  tff(c_601, plain, (![D_128, A_129]: (r2_hidden(D_128, A_129) | ~r2_hidden(D_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_579])).
% 6.13/2.41  tff(c_613, plain, (![A_129]: (r2_hidden('#skF_1'(k1_xboole_0), A_129) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_601])).
% 6.13/2.41  tff(c_614, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_613])).
% 6.13/2.41  tff(c_532, plain, (![A_114, B_115]: (r2_hidden('#skF_4'(A_114, B_115), A_114) | r1_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.13/2.41  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.13/2.41  tff(c_545, plain, (![A_116, B_117]: (~v1_xboole_0(A_116) | r1_xboole_0(A_116, B_117))), inference(resolution, [status(thm)], [c_532, c_4])).
% 6.13/2.41  tff(c_52, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.13/2.41  tff(c_551, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=A_116 | ~v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_545, c_52])).
% 6.13/2.41  tff(c_619, plain, (![B_117]: (k4_xboole_0(k1_xboole_0, B_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_614, c_551])).
% 6.13/2.41  tff(c_56, plain, (![B_35, A_34]: (k2_tarski(B_35, A_34)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.13/2.41  tff(c_159, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.13/2.41  tff(c_238, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_56, c_159])).
% 6.13/2.41  tff(c_66, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.13/2.41  tff(c_265, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_238, c_66])).
% 6.13/2.41  tff(c_281, plain, (![A_81]: (k2_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_265, c_42])).
% 6.13/2.41  tff(c_650, plain, (![A_133, B_134]: (k4_xboole_0(k2_xboole_0(A_133, B_134), B_134)=k4_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.13/2.41  tff(c_673, plain, (![A_81]: (k4_xboole_0(k1_xboole_0, A_81)=k4_xboole_0(A_81, A_81))), inference(superposition, [status(thm), theory('equality')], [c_281, c_650])).
% 6.13/2.41  tff(c_691, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_619, c_673])).
% 6.13/2.41  tff(c_38, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.13/2.41  tff(c_202, plain, (![B_21]: (k3_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_38, c_195])).
% 6.13/2.41  tff(c_765, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k3_xboole_0(A_138, B_139))=k4_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.13/2.41  tff(c_777, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_202, c_765])).
% 6.13/2.41  tff(c_781, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_691, c_777])).
% 6.13/2.41  tff(c_58, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.41  tff(c_1069, plain, (![A_161, B_162, C_163]: (r1_tarski(k2_tarski(A_161, B_162), C_163) | ~r2_hidden(B_162, C_163) | ~r2_hidden(A_161, C_163))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.13/2.41  tff(c_4605, plain, (![A_298, C_299]: (r1_tarski(k1_tarski(A_298), C_299) | ~r2_hidden(A_298, C_299) | ~r2_hidden(A_298, C_299))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1069])).
% 6.13/2.41  tff(c_44, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.13/2.41  tff(c_6070, plain, (![A_343, C_344]: (k3_xboole_0(k1_tarski(A_343), C_344)=k1_tarski(A_343) | ~r2_hidden(A_343, C_344))), inference(resolution, [status(thm)], [c_4605, c_44])).
% 6.13/2.41  tff(c_40, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.13/2.41  tff(c_6141, plain, (![A_343, C_344]: (k5_xboole_0(k1_tarski(A_343), k1_tarski(A_343))=k4_xboole_0(k1_tarski(A_343), C_344) | ~r2_hidden(A_343, C_344))), inference(superposition, [status(thm), theory('equality')], [c_6070, c_40])).
% 6.13/2.41  tff(c_6579, plain, (![A_365, C_366]: (k4_xboole_0(k1_tarski(A_365), C_366)=k1_xboole_0 | ~r2_hidden(A_365, C_366))), inference(demodulation, [status(thm), theory('equality')], [c_781, c_6141])).
% 6.13/2.41  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.13/2.41  tff(c_6668, plain, (![C_366, A_365]: (k2_xboole_0(C_366, k1_tarski(A_365))=k2_xboole_0(C_366, k1_xboole_0) | ~r2_hidden(A_365, C_366))), inference(superposition, [status(thm), theory('equality')], [c_6579, c_48])).
% 6.13/2.41  tff(c_6751, plain, (![C_367, A_368]: (k2_xboole_0(C_367, k1_tarski(A_368))=C_367 | ~r2_hidden(A_368, C_367))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6668])).
% 6.13/2.41  tff(c_244, plain, (![B_79, A_78]: (k2_xboole_0(B_79, A_78)=k2_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_238, c_66])).
% 6.13/2.41  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.41  tff(c_264, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_74])).
% 6.13/2.41  tff(c_6841, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6751, c_264])).
% 6.13/2.41  tff(c_6914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6841])).
% 6.13/2.41  tff(c_6917, plain, (![A_369]: (r2_hidden('#skF_1'(k1_xboole_0), A_369))), inference(splitRight, [status(thm)], [c_613])).
% 6.13/2.41  tff(c_6946, plain, (![A_369]: (~v1_xboole_0(A_369))), inference(resolution, [status(thm)], [c_6917, c_4])).
% 6.13/2.41  tff(c_109, plain, (![B_60, A_61]: (~r2_hidden(B_60, A_61) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.13/2.41  tff(c_114, plain, (![A_3]: (~r2_hidden(A_3, '#skF_1'(A_3)) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_109])).
% 6.13/2.41  tff(c_6944, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_6917, c_114])).
% 6.13/2.41  tff(c_6950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6946, c_6944])).
% 6.13/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.41  
% 6.13/2.41  Inference rules
% 6.13/2.41  ----------------------
% 6.13/2.41  #Ref     : 0
% 6.13/2.41  #Sup     : 1674
% 6.13/2.41  #Fact    : 0
% 6.13/2.41  #Define  : 0
% 6.13/2.41  #Split   : 2
% 6.13/2.41  #Chain   : 0
% 6.13/2.41  #Close   : 0
% 6.13/2.41  
% 6.13/2.41  Ordering : KBO
% 6.13/2.41  
% 6.13/2.41  Simplification rules
% 6.13/2.41  ----------------------
% 6.13/2.41  #Subsume      : 334
% 6.13/2.41  #Demod        : 1285
% 6.13/2.41  #Tautology    : 869
% 6.13/2.41  #SimpNegUnit  : 29
% 6.13/2.41  #BackRed      : 7
% 6.13/2.41  
% 6.13/2.41  #Partial instantiations: 0
% 6.13/2.41  #Strategies tried      : 1
% 6.13/2.41  
% 6.13/2.41  Timing (in seconds)
% 6.13/2.41  ----------------------
% 6.31/2.41  Preprocessing        : 0.36
% 6.31/2.41  Parsing              : 0.19
% 6.31/2.41  CNF conversion       : 0.03
% 6.31/2.41  Main loop            : 1.20
% 6.31/2.41  Inferencing          : 0.36
% 6.31/2.41  Reduction            : 0.50
% 6.31/2.41  Demodulation         : 0.39
% 6.31/2.41  BG Simplification    : 0.04
% 6.31/2.41  Subsumption          : 0.23
% 6.31/2.41  Abstraction          : 0.06
% 6.31/2.41  MUC search           : 0.00
% 6.31/2.41  Cooper               : 0.00
% 6.31/2.41  Total                : 1.60
% 6.31/2.41  Index Insertion      : 0.00
% 6.31/2.41  Index Deletion       : 0.00
% 6.31/2.41  Index Matching       : 0.00
% 6.31/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
