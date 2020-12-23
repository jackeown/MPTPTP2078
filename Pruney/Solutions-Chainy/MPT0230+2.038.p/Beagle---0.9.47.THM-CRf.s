%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:02 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 104 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :   74 ( 112 expanded)
%              Number of equality atoms :   59 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_62,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1451,plain,(
    ! [A_131,B_132,C_133,D_134] : k2_xboole_0(k1_enumset1(A_131,B_132,C_133),k1_tarski(D_134)) = k2_enumset1(A_131,B_132,C_133,D_134) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1460,plain,(
    ! [A_29,B_30,D_134] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(D_134)) = k2_enumset1(A_29,A_29,B_30,D_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1451])).

tff(c_3276,plain,(
    ! [A_215,B_216,D_217] : k2_xboole_0(k2_tarski(A_215,B_216),k1_tarski(D_217)) = k1_enumset1(A_215,B_216,D_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1460])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_294,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_313,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_294])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [B_70,A_71] : k3_xboole_0(B_70,A_71) = k3_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [B_61] : k3_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_148,plain,(
    ! [B_70] : k3_xboole_0(B_70,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_101])).

tff(c_322,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_331,plain,(
    ! [B_70] : k5_xboole_0(B_70,k1_xboole_0) = k4_xboole_0(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_322])).

tff(c_346,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_331])).

tff(c_408,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_427,plain,(
    ! [B_70] : k4_xboole_0(B_70,B_70) = k3_xboole_0(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_408])).

tff(c_438,plain,(
    ! [B_70] : k4_xboole_0(B_70,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_427])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_343,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_322])).

tff(c_441,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_343])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_601,plain,(
    ! [A_102,B_103] : k3_xboole_0(k3_xboole_0(A_102,B_103),A_102) = k3_xboole_0(A_102,B_103) ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_610,plain,(
    ! [A_102,B_103] : k5_xboole_0(k3_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_103)) = k4_xboole_0(k3_xboole_0(A_102,B_103),A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_6])).

tff(c_676,plain,(
    ! [A_104,B_105] : k4_xboole_0(k3_xboole_0(A_104,B_105),A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_610])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_681,plain,(
    ! [A_104,B_105] : k2_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k5_xboole_0(A_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_18])).

tff(c_727,plain,(
    ! [A_106,B_107] : k2_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_681])).

tff(c_833,plain,(
    ! [A_113,B_114] : k2_xboole_0(A_113,k3_xboole_0(B_114,A_113)) = A_113 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_727])).

tff(c_853,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_833])).

tff(c_3282,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3276,c_853])).

tff(c_22,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3310,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3282,c_22])).

tff(c_2025,plain,(
    ! [E_141,C_142,B_143,A_144] :
      ( E_141 = C_142
      | E_141 = B_143
      | E_141 = A_144
      | ~ r2_hidden(E_141,k1_enumset1(A_144,B_143,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2028,plain,(
    ! [E_141,B_30,A_29] :
      ( E_141 = B_30
      | E_141 = A_29
      | E_141 = A_29
      | ~ r2_hidden(E_141,k2_tarski(A_29,B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2025])).

tff(c_3343,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3310,c_2028])).

tff(c_3347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_60,c_3343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.81  
% 4.37/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.81  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.37/1.81  
% 4.37/1.81  %Foreground sorts:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Background operators:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Foreground operators:
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.37/1.81  
% 4.37/1.82  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.37/1.82  tff(f_70, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.37/1.82  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.37/1.82  tff(f_64, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.37/1.82  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.37/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.37/1.82  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.37/1.82  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.37/1.82  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.37/1.82  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.37/1.82  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.37/1.82  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.37/1.82  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.37/1.82  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.37/1.82  tff(c_62, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.37/1.82  tff(c_60, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.37/1.82  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.82  tff(c_48, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.37/1.82  tff(c_1451, plain, (![A_131, B_132, C_133, D_134]: (k2_xboole_0(k1_enumset1(A_131, B_132, C_133), k1_tarski(D_134))=k2_enumset1(A_131, B_132, C_133, D_134))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.37/1.82  tff(c_1460, plain, (![A_29, B_30, D_134]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(D_134))=k2_enumset1(A_29, A_29, B_30, D_134))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1451])).
% 4.37/1.82  tff(c_3276, plain, (![A_215, B_216, D_217]: (k2_xboole_0(k2_tarski(A_215, B_216), k1_tarski(D_217))=k1_enumset1(A_215, B_216, D_217))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1460])).
% 4.37/1.82  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.37/1.82  tff(c_294, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.82  tff(c_313, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_64, c_294])).
% 4.37/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.82  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.82  tff(c_132, plain, (![B_70, A_71]: (k3_xboole_0(B_70, A_71)=k3_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.82  tff(c_93, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.82  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.37/1.82  tff(c_101, plain, (![B_61]: (k3_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_93, c_12])).
% 4.37/1.82  tff(c_148, plain, (![B_70]: (k3_xboole_0(B_70, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_101])).
% 4.37/1.82  tff(c_322, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.82  tff(c_331, plain, (![B_70]: (k5_xboole_0(B_70, k1_xboole_0)=k4_xboole_0(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_322])).
% 4.37/1.82  tff(c_346, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_331])).
% 4.37/1.82  tff(c_408, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.82  tff(c_427, plain, (![B_70]: (k4_xboole_0(B_70, B_70)=k3_xboole_0(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_346, c_408])).
% 4.37/1.82  tff(c_438, plain, (![B_70]: (k4_xboole_0(B_70, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_427])).
% 4.37/1.82  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.37/1.82  tff(c_343, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_322])).
% 4.37/1.82  tff(c_441, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_438, c_343])).
% 4.37/1.82  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.82  tff(c_601, plain, (![A_102, B_103]: (k3_xboole_0(k3_xboole_0(A_102, B_103), A_102)=k3_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_8, c_294])).
% 4.37/1.82  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.82  tff(c_610, plain, (![A_102, B_103]: (k5_xboole_0(k3_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_103))=k4_xboole_0(k3_xboole_0(A_102, B_103), A_102))), inference(superposition, [status(thm), theory('equality')], [c_601, c_6])).
% 4.37/1.82  tff(c_676, plain, (![A_104, B_105]: (k4_xboole_0(k3_xboole_0(A_104, B_105), A_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_441, c_610])).
% 4.37/1.82  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.82  tff(c_681, plain, (![A_104, B_105]: (k2_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k5_xboole_0(A_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_676, c_18])).
% 4.37/1.82  tff(c_727, plain, (![A_106, B_107]: (k2_xboole_0(A_106, k3_xboole_0(A_106, B_107))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_681])).
% 4.37/1.82  tff(c_833, plain, (![A_113, B_114]: (k2_xboole_0(A_113, k3_xboole_0(B_114, A_113))=A_113)), inference(superposition, [status(thm), theory('equality')], [c_2, c_727])).
% 4.37/1.82  tff(c_853, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_313, c_833])).
% 4.37/1.82  tff(c_3282, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3276, c_853])).
% 4.37/1.82  tff(c_22, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.37/1.82  tff(c_3310, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3282, c_22])).
% 4.37/1.82  tff(c_2025, plain, (![E_141, C_142, B_143, A_144]: (E_141=C_142 | E_141=B_143 | E_141=A_144 | ~r2_hidden(E_141, k1_enumset1(A_144, B_143, C_142)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.37/1.82  tff(c_2028, plain, (![E_141, B_30, A_29]: (E_141=B_30 | E_141=A_29 | E_141=A_29 | ~r2_hidden(E_141, k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2025])).
% 4.37/1.82  tff(c_3343, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3310, c_2028])).
% 4.37/1.82  tff(c_3347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_60, c_3343])).
% 4.37/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.82  
% 4.37/1.82  Inference rules
% 4.37/1.82  ----------------------
% 4.37/1.82  #Ref     : 0
% 4.37/1.82  #Sup     : 788
% 4.37/1.82  #Fact    : 0
% 4.37/1.82  #Define  : 0
% 4.37/1.82  #Split   : 0
% 4.37/1.82  #Chain   : 0
% 4.37/1.82  #Close   : 0
% 4.37/1.82  
% 4.37/1.82  Ordering : KBO
% 4.37/1.82  
% 4.37/1.82  Simplification rules
% 4.37/1.82  ----------------------
% 4.37/1.82  #Subsume      : 24
% 4.37/1.82  #Demod        : 946
% 4.37/1.82  #Tautology    : 677
% 4.37/1.82  #SimpNegUnit  : 1
% 4.37/1.82  #BackRed      : 1
% 4.37/1.82  
% 4.37/1.82  #Partial instantiations: 0
% 4.37/1.82  #Strategies tried      : 1
% 4.37/1.82  
% 4.37/1.82  Timing (in seconds)
% 4.37/1.82  ----------------------
% 4.37/1.83  Preprocessing        : 0.41
% 4.37/1.83  Parsing              : 0.21
% 4.37/1.83  CNF conversion       : 0.03
% 4.37/1.83  Main loop            : 0.66
% 4.37/1.83  Inferencing          : 0.20
% 4.37/1.83  Reduction            : 0.30
% 4.37/1.83  Demodulation         : 0.26
% 4.37/1.83  BG Simplification    : 0.03
% 4.37/1.83  Subsumption          : 0.09
% 4.37/1.83  Abstraction          : 0.04
% 4.37/1.83  MUC search           : 0.00
% 4.37/1.83  Cooper               : 0.00
% 4.37/1.83  Total                : 1.10
% 4.37/1.83  Index Insertion      : 0.00
% 4.37/1.83  Index Deletion       : 0.00
% 4.37/1.83  Index Matching       : 0.00
% 4.37/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
