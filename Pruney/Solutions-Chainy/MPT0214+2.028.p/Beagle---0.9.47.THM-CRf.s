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
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 107 expanded)
%              Number of leaves         :   44 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 109 expanded)
%              Number of equality atoms :   53 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_93,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_64,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1718,plain,(
    ! [A_168,B_169,C_170,D_171] : k2_xboole_0(k1_enumset1(A_168,B_169,C_170),k1_tarski(D_171)) = k2_enumset1(A_168,B_169,C_170,D_171) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1727,plain,(
    ! [A_40,B_41,D_171] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(D_171)) = k2_enumset1(A_40,A_40,B_41,D_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1718])).

tff(c_1731,plain,(
    ! [A_172,B_173,D_174] : k2_xboole_0(k2_tarski(A_172,B_173),k1_tarski(D_174)) = k1_enumset1(A_172,B_173,D_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1727])).

tff(c_1740,plain,(
    ! [A_39,D_174] : k2_xboole_0(k1_tarski(A_39),k1_tarski(D_174)) = k1_enumset1(A_39,A_39,D_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1731])).

tff(c_1744,plain,(
    ! [A_175,D_176] : k2_xboole_0(k1_tarski(A_175),k1_tarski(D_176)) = k2_tarski(A_175,D_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1740])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_121,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | ~ r1_xboole_0(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_316,plain,(
    ! [A_109,B_110,C_111] :
      ( ~ r1_xboole_0(A_109,B_110)
      | ~ r2_hidden(C_111,k3_xboole_0(A_109,B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_347,plain,(
    ! [A_115,B_116] :
      ( ~ r1_xboole_0(A_115,B_116)
      | k3_xboole_0(A_115,B_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_316])).

tff(c_375,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_347])).

tff(c_377,plain,(
    ! [B_117,A_118] : k3_xboole_0(B_117,k4_xboole_0(A_118,B_117)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_347])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_385,plain,(
    ! [B_117,A_118] : k4_xboole_0(B_117,k4_xboole_0(A_118,B_117)) = k5_xboole_0(B_117,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_12])).

tff(c_435,plain,(
    ! [B_121,A_122] : k4_xboole_0(B_121,k4_xboole_0(A_122,B_121)) = B_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_385])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_459,plain,(
    ! [B_121,A_122] : k3_xboole_0(B_121,k4_xboole_0(A_122,B_121)) = k4_xboole_0(B_121,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_16])).

tff(c_491,plain,(
    ! [B_121] : k4_xboole_0(B_121,B_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_459])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_247,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_235])).

tff(c_535,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_247])).

tff(c_78,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_132,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_132])).

tff(c_244,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_235])).

tff(c_779,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_244])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_796,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_22])).

tff(c_817,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_796])).

tff(c_1750,plain,(
    k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1744,c_817])).

tff(c_137,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_149,plain,(
    ! [B_92,A_91] : r2_hidden(B_92,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_1775,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1750,c_149])).

tff(c_48,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1786,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1775,c_48])).

tff(c_1790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.60  
% 3.16/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.16/1.60  
% 3.16/1.60  %Foreground sorts:
% 3.16/1.60  
% 3.16/1.60  
% 3.16/1.60  %Background operators:
% 3.16/1.60  
% 3.16/1.60  
% 3.16/1.60  %Foreground operators:
% 3.16/1.60  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.16/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.16/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.16/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.16/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.16/1.60  
% 3.16/1.62  tff(f_110, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.16/1.62  tff(f_95, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.16/1.62  tff(f_93, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.62  tff(f_97, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.16/1.62  tff(f_91, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.16/1.62  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.16/1.62  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.16/1.62  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.16/1.62  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.62  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.16/1.62  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.16/1.62  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.16/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.16/1.62  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.16/1.62  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.16/1.62  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.16/1.62  tff(f_89, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.16/1.62  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.16/1.62  tff(c_64, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.62  tff(c_62, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.62  tff(c_66, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.62  tff(c_1718, plain, (![A_168, B_169, C_170, D_171]: (k2_xboole_0(k1_enumset1(A_168, B_169, C_170), k1_tarski(D_171))=k2_enumset1(A_168, B_169, C_170, D_171))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.62  tff(c_1727, plain, (![A_40, B_41, D_171]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(D_171))=k2_enumset1(A_40, A_40, B_41, D_171))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1718])).
% 3.16/1.62  tff(c_1731, plain, (![A_172, B_173, D_174]: (k2_xboole_0(k2_tarski(A_172, B_173), k1_tarski(D_174))=k1_enumset1(A_172, B_173, D_174))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1727])).
% 3.16/1.62  tff(c_1740, plain, (![A_39, D_174]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(D_174))=k1_enumset1(A_39, A_39, D_174))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1731])).
% 3.16/1.62  tff(c_1744, plain, (![A_175, D_176]: (k2_xboole_0(k1_tarski(A_175), k1_tarski(D_176))=k2_tarski(A_175, D_176))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1740])).
% 3.16/1.62  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.62  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.62  tff(c_121, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | ~r1_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.62  tff(c_124, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_20, c_121])).
% 3.16/1.62  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.62  tff(c_316, plain, (![A_109, B_110, C_111]: (~r1_xboole_0(A_109, B_110) | ~r2_hidden(C_111, k3_xboole_0(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.62  tff(c_347, plain, (![A_115, B_116]: (~r1_xboole_0(A_115, B_116) | k3_xboole_0(A_115, B_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_316])).
% 3.16/1.62  tff(c_375, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_347])).
% 3.16/1.62  tff(c_377, plain, (![B_117, A_118]: (k3_xboole_0(B_117, k4_xboole_0(A_118, B_117))=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_347])).
% 3.16/1.62  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.62  tff(c_385, plain, (![B_117, A_118]: (k4_xboole_0(B_117, k4_xboole_0(A_118, B_117))=k5_xboole_0(B_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_377, c_12])).
% 3.16/1.62  tff(c_435, plain, (![B_121, A_122]: (k4_xboole_0(B_121, k4_xboole_0(A_122, B_121))=B_121)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_385])).
% 3.16/1.62  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.62  tff(c_459, plain, (![B_121, A_122]: (k3_xboole_0(B_121, k4_xboole_0(A_122, B_121))=k4_xboole_0(B_121, B_121))), inference(superposition, [status(thm), theory('equality')], [c_435, c_16])).
% 3.16/1.62  tff(c_491, plain, (![B_121]: (k4_xboole_0(B_121, B_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_375, c_459])).
% 3.16/1.62  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.62  tff(c_235, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k4_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.62  tff(c_247, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_235])).
% 3.16/1.62  tff(c_535, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_491, c_247])).
% 3.16/1.62  tff(c_78, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.16/1.62  tff(c_132, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.62  tff(c_136, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_78, c_132])).
% 3.16/1.62  tff(c_244, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_235])).
% 3.16/1.62  tff(c_779, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_535, c_244])).
% 3.16/1.62  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.62  tff(c_796, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_779, c_22])).
% 3.16/1.62  tff(c_817, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_796])).
% 3.16/1.62  tff(c_1750, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1744, c_817])).
% 3.16/1.62  tff(c_137, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.62  tff(c_26, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.62  tff(c_149, plain, (![B_92, A_91]: (r2_hidden(B_92, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_26])).
% 3.16/1.62  tff(c_1775, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1750, c_149])).
% 3.16/1.62  tff(c_48, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.62  tff(c_1786, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_1775, c_48])).
% 3.16/1.62  tff(c_1790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1786])).
% 3.16/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.62  
% 3.16/1.62  Inference rules
% 3.16/1.62  ----------------------
% 3.16/1.62  #Ref     : 0
% 3.16/1.62  #Sup     : 411
% 3.16/1.62  #Fact    : 0
% 3.16/1.62  #Define  : 0
% 3.16/1.62  #Split   : 1
% 3.16/1.62  #Chain   : 0
% 3.16/1.62  #Close   : 0
% 3.16/1.62  
% 3.16/1.62  Ordering : KBO
% 3.16/1.62  
% 3.16/1.62  Simplification rules
% 3.16/1.62  ----------------------
% 3.16/1.62  #Subsume      : 15
% 3.16/1.62  #Demod        : 365
% 3.16/1.62  #Tautology    : 320
% 3.16/1.62  #SimpNegUnit  : 9
% 3.16/1.62  #BackRed      : 4
% 3.16/1.62  
% 3.16/1.62  #Partial instantiations: 0
% 3.16/1.62  #Strategies tried      : 1
% 3.16/1.62  
% 3.16/1.62  Timing (in seconds)
% 3.16/1.62  ----------------------
% 3.16/1.62  Preprocessing        : 0.33
% 3.16/1.62  Parsing              : 0.17
% 3.16/1.62  CNF conversion       : 0.03
% 3.16/1.62  Main loop            : 0.44
% 3.16/1.62  Inferencing          : 0.15
% 3.16/1.62  Reduction            : 0.17
% 3.16/1.62  Demodulation         : 0.13
% 3.16/1.62  BG Simplification    : 0.02
% 3.16/1.62  Subsumption          : 0.07
% 3.16/1.62  Abstraction          : 0.02
% 3.16/1.62  MUC search           : 0.00
% 3.16/1.62  Cooper               : 0.00
% 3.16/1.62  Total                : 0.80
% 3.16/1.62  Index Insertion      : 0.00
% 3.16/1.62  Index Deletion       : 0.00
% 3.16/1.62  Index Matching       : 0.00
% 3.16/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
