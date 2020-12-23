%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   37 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  106 ( 209 expanded)
%              Number of equality atoms :   40 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_102,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_72,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_348,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,A_86)
      | ~ r2_hidden(D_85,k4_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_358,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_86,B_87)),A_86)
      | v1_xboole_0(k4_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_348])).

tff(c_387,plain,(
    ! [D_92,B_93,A_94] :
      ( ~ r2_hidden(D_92,B_93)
      | ~ r2_hidden(D_92,k4_xboole_0(A_94,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1494,plain,(
    ! [A_203,B_204] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_203,B_204)),B_204)
      | v1_xboole_0(k4_xboole_0(A_203,B_204)) ) ),
    inference(resolution,[status(thm)],[c_4,c_387])).

tff(c_1521,plain,(
    ! [A_205] : v1_xboole_0(k4_xboole_0(A_205,A_205)) ),
    inference(resolution,[status(thm)],[c_358,c_1494])).

tff(c_40,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,B_66)
      | ~ r1_tarski(k1_tarski(A_65),B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_174,plain,(
    ! [A_65] : r2_hidden(A_65,k1_tarski(A_65)) ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_54,plain,(
    ! [B_34,A_33] : k2_tarski(B_34,A_33) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_175,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_226,plain,(
    ! [B_74,A_75] : k3_tarski(k2_tarski(B_74,A_75)) = k2_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_175])).

tff(c_68,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_253,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_68])).

tff(c_269,plain,(
    ! [A_77] : k2_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_44])).

tff(c_368,plain,(
    ! [A_90,B_91] : k2_xboole_0(A_90,k4_xboole_0(B_91,A_90)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_375,plain,(
    ! [B_91] : k4_xboole_0(B_91,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_269])).

tff(c_398,plain,(
    ! [B_95] : k4_xboole_0(B_95,k1_xboole_0) = B_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_375])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_457,plain,(
    ! [D_101,B_102] :
      ( ~ r2_hidden(D_101,k1_xboole_0)
      | ~ r2_hidden(D_101,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_14])).

tff(c_470,plain,(
    ! [B_102] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_102)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_457])).

tff(c_472,plain,(
    ! [B_103] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_103) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_481,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_174,c_472])).

tff(c_482,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_556,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_2'(A_108,B_109),A_108)
      | r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_580,plain,(
    ! [A_108,B_109] :
      ( ~ v1_xboole_0(A_108)
      | r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_556,c_2])).

tff(c_581,plain,(
    ! [A_110,B_111] :
      ( ~ v1_xboole_0(A_110)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_556,c_2])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | ~ r1_tarski(B_22,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_750,plain,(
    ! [B_125,A_126] :
      ( B_125 = A_126
      | ~ r1_tarski(B_125,A_126)
      | ~ v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_581,c_36])).

tff(c_773,plain,(
    ! [B_130,A_131] :
      ( B_130 = A_131
      | ~ v1_xboole_0(B_130)
      | ~ v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_580,c_750])).

tff(c_776,plain,(
    ! [A_131] :
      ( k1_xboole_0 = A_131
      | ~ v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_482,c_773])).

tff(c_1551,plain,(
    ! [A_205] : k4_xboole_0(A_205,A_205) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1521,c_776])).

tff(c_137,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,(
    ! [B_22] : k3_xboole_0(B_22,B_22) = B_22 ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_483,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_500,plain,(
    ! [B_22] : k5_xboole_0(B_22,B_22) = k4_xboole_0(B_22,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_483])).

tff(c_160,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tarski(A_63),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1017,plain,(
    ! [A_160,B_161] :
      ( k3_xboole_0(k1_tarski(A_160),B_161) = k1_tarski(A_160)
      | ~ r2_hidden(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_160,c_46])).

tff(c_42,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1023,plain,(
    ! [A_160,B_161] :
      ( k5_xboole_0(k1_tarski(A_160),k1_tarski(A_160)) = k4_xboole_0(k1_tarski(A_160),B_161)
      | ~ r2_hidden(A_160,B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_42])).

tff(c_1036,plain,(
    ! [A_160,B_161] :
      ( k4_xboole_0(k1_tarski(A_160),k1_tarski(A_160)) = k4_xboole_0(k1_tarski(A_160),B_161)
      | ~ r2_hidden(A_160,B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_1023])).

tff(c_15518,plain,(
    ! [A_829,B_830] :
      ( k4_xboole_0(k1_tarski(A_829),B_830) = k1_xboole_0
      | ~ r2_hidden(A_829,B_830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_1036])).

tff(c_48,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_15932,plain,(
    ! [B_830,A_829] :
      ( k2_xboole_0(B_830,k1_tarski(A_829)) = k2_xboole_0(B_830,k1_xboole_0)
      | ~ r2_hidden(A_829,B_830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15518,c_48])).

tff(c_16088,plain,(
    ! [B_833,A_834] :
      ( k2_xboole_0(B_833,k1_tarski(A_834)) = B_833
      | ~ r2_hidden(A_834,B_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_15932])).

tff(c_232,plain,(
    ! [B_74,A_75] : k2_xboole_0(B_74,A_75) = k2_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_68])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_252,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_70])).

tff(c_16110,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16088,c_252])).

tff(c_16159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_16110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.68/3.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/3.30  
% 8.82/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/3.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 8.82/3.30  
% 8.82/3.30  %Foreground sorts:
% 8.82/3.30  
% 8.82/3.30  
% 8.82/3.30  %Background operators:
% 8.82/3.30  
% 8.82/3.30  
% 8.82/3.30  %Foreground operators:
% 8.82/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.82/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.82/3.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.82/3.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.82/3.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.82/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.82/3.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.82/3.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.82/3.30  tff('#skF_7', type, '#skF_7': $i).
% 8.82/3.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.82/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.82/3.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.82/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.82/3.30  tff('#skF_6', type, '#skF_6': $i).
% 8.82/3.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.82/3.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.82/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.82/3.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.82/3.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.82/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.82/3.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.82/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.82/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.82/3.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.82/3.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.82/3.30  
% 8.82/3.32  tff(f_107, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.82/3.32  tff(f_76, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.82/3.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.82/3.32  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.82/3.32  tff(f_72, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.82/3.32  tff(f_100, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.82/3.32  tff(f_88, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.82/3.32  tff(f_102, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.82/3.32  tff(f_82, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.82/3.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.82/3.32  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.82/3.32  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.82/3.32  tff(c_72, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.82/3.32  tff(c_44, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.82/3.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.82/3.32  tff(c_348, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, A_86) | ~r2_hidden(D_85, k4_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.82/3.32  tff(c_358, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(k4_xboole_0(A_86, B_87)), A_86) | v1_xboole_0(k4_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_4, c_348])).
% 8.82/3.32  tff(c_387, plain, (![D_92, B_93, A_94]: (~r2_hidden(D_92, B_93) | ~r2_hidden(D_92, k4_xboole_0(A_94, B_93)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.82/3.32  tff(c_1494, plain, (![A_203, B_204]: (~r2_hidden('#skF_1'(k4_xboole_0(A_203, B_204)), B_204) | v1_xboole_0(k4_xboole_0(A_203, B_204)))), inference(resolution, [status(thm)], [c_4, c_387])).
% 8.82/3.32  tff(c_1521, plain, (![A_205]: (v1_xboole_0(k4_xboole_0(A_205, A_205)))), inference(resolution, [status(thm)], [c_358, c_1494])).
% 8.82/3.32  tff(c_40, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.82/3.32  tff(c_165, plain, (![A_65, B_66]: (r2_hidden(A_65, B_66) | ~r1_tarski(k1_tarski(A_65), B_66))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.82/3.32  tff(c_174, plain, (![A_65]: (r2_hidden(A_65, k1_tarski(A_65)))), inference(resolution, [status(thm)], [c_40, c_165])).
% 8.82/3.32  tff(c_54, plain, (![B_34, A_33]: (k2_tarski(B_34, A_33)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.82/3.32  tff(c_175, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.82/3.32  tff(c_226, plain, (![B_74, A_75]: (k3_tarski(k2_tarski(B_74, A_75))=k2_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_54, c_175])).
% 8.82/3.32  tff(c_68, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.82/3.32  tff(c_253, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_226, c_68])).
% 8.82/3.32  tff(c_269, plain, (![A_77]: (k2_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_253, c_44])).
% 8.82/3.32  tff(c_368, plain, (![A_90, B_91]: (k2_xboole_0(A_90, k4_xboole_0(B_91, A_90))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.82/3.32  tff(c_375, plain, (![B_91]: (k4_xboole_0(B_91, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_91))), inference(superposition, [status(thm), theory('equality')], [c_368, c_269])).
% 8.82/3.32  tff(c_398, plain, (![B_95]: (k4_xboole_0(B_95, k1_xboole_0)=B_95)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_375])).
% 8.82/3.32  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.82/3.32  tff(c_457, plain, (![D_101, B_102]: (~r2_hidden(D_101, k1_xboole_0) | ~r2_hidden(D_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_398, c_14])).
% 8.82/3.32  tff(c_470, plain, (![B_102]: (~r2_hidden('#skF_1'(k1_xboole_0), B_102) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_457])).
% 8.82/3.32  tff(c_472, plain, (![B_103]: (~r2_hidden('#skF_1'(k1_xboole_0), B_103))), inference(splitLeft, [status(thm)], [c_470])).
% 8.82/3.32  tff(c_481, plain, $false, inference(resolution, [status(thm)], [c_174, c_472])).
% 8.82/3.32  tff(c_482, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_470])).
% 8.82/3.32  tff(c_556, plain, (![A_108, B_109]: (r2_hidden('#skF_2'(A_108, B_109), A_108) | r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.82/3.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.82/3.32  tff(c_580, plain, (![A_108, B_109]: (~v1_xboole_0(A_108) | r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_556, c_2])).
% 8.82/3.32  tff(c_581, plain, (![A_110, B_111]: (~v1_xboole_0(A_110) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_556, c_2])).
% 8.82/3.32  tff(c_36, plain, (![B_22, A_21]: (B_22=A_21 | ~r1_tarski(B_22, A_21) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.82/3.32  tff(c_750, plain, (![B_125, A_126]: (B_125=A_126 | ~r1_tarski(B_125, A_126) | ~v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_581, c_36])).
% 8.82/3.32  tff(c_773, plain, (![B_130, A_131]: (B_130=A_131 | ~v1_xboole_0(B_130) | ~v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_580, c_750])).
% 8.82/3.32  tff(c_776, plain, (![A_131]: (k1_xboole_0=A_131 | ~v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_482, c_773])).
% 8.82/3.32  tff(c_1551, plain, (![A_205]: (k4_xboole_0(A_205, A_205)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1521, c_776])).
% 8.82/3.32  tff(c_137, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.82/3.32  tff(c_141, plain, (![B_22]: (k3_xboole_0(B_22, B_22)=B_22)), inference(resolution, [status(thm)], [c_40, c_137])).
% 8.82/3.32  tff(c_483, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k4_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.82/3.32  tff(c_500, plain, (![B_22]: (k5_xboole_0(B_22, B_22)=k4_xboole_0(B_22, B_22))), inference(superposition, [status(thm), theory('equality')], [c_141, c_483])).
% 8.82/3.32  tff(c_160, plain, (![A_63, B_64]: (r1_tarski(k1_tarski(A_63), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.82/3.32  tff(c_46, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.82/3.32  tff(c_1017, plain, (![A_160, B_161]: (k3_xboole_0(k1_tarski(A_160), B_161)=k1_tarski(A_160) | ~r2_hidden(A_160, B_161))), inference(resolution, [status(thm)], [c_160, c_46])).
% 8.82/3.32  tff(c_42, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.82/3.32  tff(c_1023, plain, (![A_160, B_161]: (k5_xboole_0(k1_tarski(A_160), k1_tarski(A_160))=k4_xboole_0(k1_tarski(A_160), B_161) | ~r2_hidden(A_160, B_161))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_42])).
% 8.82/3.32  tff(c_1036, plain, (![A_160, B_161]: (k4_xboole_0(k1_tarski(A_160), k1_tarski(A_160))=k4_xboole_0(k1_tarski(A_160), B_161) | ~r2_hidden(A_160, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_500, c_1023])).
% 8.82/3.32  tff(c_15518, plain, (![A_829, B_830]: (k4_xboole_0(k1_tarski(A_829), B_830)=k1_xboole_0 | ~r2_hidden(A_829, B_830))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_1036])).
% 8.82/3.32  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.82/3.32  tff(c_15932, plain, (![B_830, A_829]: (k2_xboole_0(B_830, k1_tarski(A_829))=k2_xboole_0(B_830, k1_xboole_0) | ~r2_hidden(A_829, B_830))), inference(superposition, [status(thm), theory('equality')], [c_15518, c_48])).
% 8.82/3.32  tff(c_16088, plain, (![B_833, A_834]: (k2_xboole_0(B_833, k1_tarski(A_834))=B_833 | ~r2_hidden(A_834, B_833))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_15932])).
% 8.82/3.32  tff(c_232, plain, (![B_74, A_75]: (k2_xboole_0(B_74, A_75)=k2_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_226, c_68])).
% 8.82/3.32  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_6'), '#skF_7')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.82/3.32  tff(c_252, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_70])).
% 8.82/3.32  tff(c_16110, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16088, c_252])).
% 8.82/3.32  tff(c_16159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_16110])).
% 8.82/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/3.32  
% 8.82/3.32  Inference rules
% 8.82/3.32  ----------------------
% 8.82/3.32  #Ref     : 0
% 8.82/3.32  #Sup     : 4089
% 8.82/3.32  #Fact    : 0
% 8.82/3.32  #Define  : 0
% 8.82/3.32  #Split   : 6
% 8.82/3.32  #Chain   : 0
% 8.82/3.32  #Close   : 0
% 8.82/3.32  
% 8.82/3.32  Ordering : KBO
% 8.82/3.32  
% 8.82/3.32  Simplification rules
% 8.82/3.32  ----------------------
% 8.82/3.32  #Subsume      : 2091
% 8.82/3.32  #Demod        : 1508
% 8.82/3.32  #Tautology    : 868
% 8.82/3.32  #SimpNegUnit  : 100
% 8.82/3.32  #BackRed      : 46
% 8.82/3.32  
% 8.82/3.32  #Partial instantiations: 0
% 8.82/3.32  #Strategies tried      : 1
% 8.82/3.32  
% 8.82/3.32  Timing (in seconds)
% 8.82/3.32  ----------------------
% 8.82/3.32  Preprocessing        : 0.35
% 8.82/3.32  Parsing              : 0.19
% 8.82/3.32  CNF conversion       : 0.02
% 8.82/3.32  Main loop            : 2.16
% 8.82/3.32  Inferencing          : 0.58
% 8.82/3.32  Reduction            : 0.70
% 8.82/3.32  Demodulation         : 0.51
% 8.82/3.32  BG Simplification    : 0.06
% 8.82/3.32  Subsumption          : 0.68
% 8.82/3.32  Abstraction          : 0.09
% 8.82/3.32  MUC search           : 0.00
% 8.82/3.32  Cooper               : 0.00
% 8.82/3.32  Total                : 2.54
% 8.82/3.32  Index Insertion      : 0.00
% 8.82/3.32  Index Deletion       : 0.00
% 8.82/3.32  Index Matching       : 0.00
% 8.82/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
