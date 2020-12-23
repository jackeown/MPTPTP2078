%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 304 expanded)
%              Number of leaves         :   33 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  113 ( 363 expanded)
%              Number of equality atoms :   75 ( 249 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_365,plain,(
    ! [A_62,B_63] : k4_xboole_0(k2_xboole_0(A_62,B_63),B_63) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_375,plain,(
    ! [A_62] : k4_xboole_0(A_62,k1_xboole_0) = k2_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_18])).

tff(c_407,plain,(
    ! [A_64] : k2_xboole_0(A_64,k1_xboole_0) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_375])).

tff(c_440,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_530,plain,(
    ! [A_67,B_68] : k2_xboole_0(k3_xboole_0(A_67,B_68),k4_xboole_0(A_67,B_68)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_67,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_82,plain,(
    ! [A_44,B_43] : r1_tarski(A_44,k2_xboole_0(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_34])).

tff(c_539,plain,(
    ! [A_67,B_68] : r1_tarski(k4_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_82])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_981,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_xboole_0(A_78,C_79)
      | ~ r1_xboole_0(B_80,C_79)
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1091,plain,(
    ! [A_82] :
      ( r1_xboole_0(A_82,'#skF_3')
      | ~ r1_tarski(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_981])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_239,plain,(
    ! [A_54,B_55] :
      ( ~ r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_228])).

tff(c_1574,plain,(
    ! [A_96] :
      ( k3_xboole_0(A_96,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_96,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1091,c_239])).

tff(c_1612,plain,(
    ! [B_68] : k3_xboole_0(k4_xboole_0('#skF_5',B_68),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_539,c_1574])).

tff(c_42,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_43,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_131,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_34])).

tff(c_1182,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(k4_xboole_0(A_83,B_84),C_85)
      | ~ r1_tarski(A_83,k2_xboole_0(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11292,plain,(
    ! [A_239,B_240,C_241] :
      ( k2_xboole_0(k4_xboole_0(A_239,B_240),C_241) = C_241
      | ~ r1_tarski(A_239,k2_xboole_0(B_240,C_241)) ) ),
    inference(resolution,[status(thm)],[c_1182,c_14])).

tff(c_11490,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_11292])).

tff(c_618,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_34])).

tff(c_1690,plain,(
    ! [A_97,B_98] : k2_xboole_0(k3_xboole_0(A_97,B_98),A_97) = A_97 ),
    inference(resolution,[status(thm)],[c_618,c_14])).

tff(c_403,plain,(
    ! [A_62] : k2_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_375])).

tff(c_2153,plain,(
    ! [B_104] : k3_xboole_0(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1690,c_403])).

tff(c_2202,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2153])).

tff(c_757,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_799,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_757])).

tff(c_2268,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_799])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1384,plain,(
    ! [A_92,B_93,C_94] : k2_xboole_0(k2_xboole_0(A_92,B_93),C_94) = k2_xboole_0(A_92,k2_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3968,plain,(
    ! [A_148,C_149] : k2_xboole_0(A_148,k2_xboole_0(A_148,C_149)) = k2_xboole_0(A_148,C_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1384])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3998,plain,(
    ! [A_148,C_149] : k4_xboole_0(k2_xboole_0(A_148,C_149),k2_xboole_0(A_148,C_149)) = k4_xboole_0(A_148,k2_xboole_0(A_148,C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_20])).

tff(c_6321,plain,(
    ! [A_178,C_179] : k4_xboole_0(A_178,k2_xboole_0(A_178,C_179)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_3998])).

tff(c_572,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_530])).

tff(c_6344,plain,(
    ! [A_178,C_179] : k2_xboole_0(k3_xboole_0(k2_xboole_0(A_178,C_179),A_178),k1_xboole_0) = A_178 ),
    inference(superposition,[status(thm),theory(equality)],[c_6321,c_572])).

tff(c_6450,plain,(
    ! [A_178,C_179] : k3_xboole_0(A_178,k2_xboole_0(A_178,C_179)) = A_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_2,c_4,c_6344])).

tff(c_11705,plain,(
    k3_xboole_0(k4_xboole_0('#skF_5','#skF_4'),'#skF_3') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11490,c_6450])).

tff(c_11756,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_11705])).

tff(c_30,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12006,plain,(
    k2_xboole_0(k3_xboole_0('#skF_5','#skF_4'),k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_11756,c_30])).

tff(c_12026,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_2,c_4,c_12006])).

tff(c_640,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_xboole_0(A_69,B_70),A_69) = A_69 ),
    inference(resolution,[status(thm)],[c_618,c_14])).

tff(c_12361,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12026,c_640])).

tff(c_38,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_240,plain,(
    ! [A_57,B_58] :
      ( ~ r1_xboole_0(A_57,B_58)
      | k3_xboole_0(A_57,B_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_228])).

tff(c_247,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_240])).

tff(c_265,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_247])).

tff(c_24,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_336,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_24])).

tff(c_339,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_336])).

tff(c_16,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12009,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11756,c_16])).

tff(c_12027,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_12009])).

tff(c_387,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_365])).

tff(c_1480,plain,(
    ! [A_5,C_94] : k2_xboole_0(A_5,k2_xboole_0(A_5,C_94)) = k2_xboole_0(A_5,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1384])).

tff(c_12600,plain,(
    ! [A_243,B_244,C_245] : k4_xboole_0(k2_xboole_0(A_243,k2_xboole_0(B_244,C_245)),C_245) = k4_xboole_0(k2_xboole_0(A_243,B_244),C_245) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_20])).

tff(c_12859,plain,(
    ! [A_246] : k4_xboole_0(k2_xboole_0(A_246,k2_xboole_0('#skF_4','#skF_3')),'#skF_6') = k4_xboole_0(k2_xboole_0(A_246,'#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_12600])).

tff(c_12931,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_6') = k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1480,c_12859])).

tff(c_12981,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_12027,c_387,c_12931])).

tff(c_645,plain,(
    ! [A_71,B_72] : r1_tarski(k4_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_82])).

tff(c_4599,plain,(
    ! [A_156,B_157] : k2_xboole_0(k4_xboole_0(A_156,B_157),A_156) = A_156 ),
    inference(resolution,[status(thm)],[c_645,c_14])).

tff(c_4687,plain,(
    ! [A_1,B_157] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_157)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4599])).

tff(c_13008,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_12981,c_4687])).

tff(c_13045,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12361,c_13008])).

tff(c_13047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_13045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:45:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.40/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.40/3.09  
% 8.40/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.40/3.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.40/3.09  
% 8.40/3.09  %Foreground sorts:
% 8.40/3.09  
% 8.40/3.09  
% 8.40/3.09  %Background operators:
% 8.40/3.09  
% 8.40/3.09  
% 8.40/3.09  %Foreground operators:
% 8.40/3.09  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.40/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.40/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.40/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.40/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.40/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.40/3.09  tff('#skF_5', type, '#skF_5': $i).
% 8.40/3.09  tff('#skF_6', type, '#skF_6': $i).
% 8.40/3.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.40/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.40/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.40/3.09  tff('#skF_4', type, '#skF_4': $i).
% 8.40/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.40/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.40/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.40/3.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.40/3.09  
% 8.51/3.11  tff(f_92, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.51/3.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.51/3.11  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.51/3.11  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.51/3.11  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.51/3.11  tff(f_75, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.51/3.11  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.51/3.11  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.51/3.11  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.51/3.11  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.51/3.11  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.51/3.11  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.51/3.11  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.51/3.11  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.51/3.11  tff(f_73, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.51/3.11  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.51/3.11  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.51/3.11  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.51/3.11  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.11  tff(c_18, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.51/3.11  tff(c_365, plain, (![A_62, B_63]: (k4_xboole_0(k2_xboole_0(A_62, B_63), B_63)=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.51/3.11  tff(c_375, plain, (![A_62]: (k4_xboole_0(A_62, k1_xboole_0)=k2_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_365, c_18])).
% 8.51/3.11  tff(c_407, plain, (![A_64]: (k2_xboole_0(A_64, k1_xboole_0)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_375])).
% 8.51/3.11  tff(c_440, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_407])).
% 8.51/3.11  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.51/3.11  tff(c_530, plain, (![A_67, B_68]: (k2_xboole_0(k3_xboole_0(A_67, B_68), k4_xboole_0(A_67, B_68))=A_67)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.51/3.11  tff(c_67, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.11  tff(c_34, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.51/3.11  tff(c_82, plain, (![A_44, B_43]: (r1_tarski(A_44, k2_xboole_0(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_34])).
% 8.51/3.11  tff(c_539, plain, (![A_67, B_68]: (r1_tarski(k4_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_530, c_82])).
% 8.51/3.11  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.51/3.11  tff(c_981, plain, (![A_78, C_79, B_80]: (r1_xboole_0(A_78, C_79) | ~r1_xboole_0(B_80, C_79) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.51/3.11  tff(c_1091, plain, (![A_82]: (r1_xboole_0(A_82, '#skF_3') | ~r1_tarski(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_981])).
% 8.51/3.11  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.51/3.11  tff(c_228, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/3.11  tff(c_239, plain, (![A_54, B_55]: (~r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_228])).
% 8.51/3.11  tff(c_1574, plain, (![A_96]: (k3_xboole_0(A_96, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_96, '#skF_5'))), inference(resolution, [status(thm)], [c_1091, c_239])).
% 8.51/3.11  tff(c_1612, plain, (![B_68]: (k3_xboole_0(k4_xboole_0('#skF_5', B_68), '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_539, c_1574])).
% 8.51/3.11  tff(c_42, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.51/3.11  tff(c_43, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 8.51/3.11  tff(c_131, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_34])).
% 8.51/3.11  tff(c_1182, plain, (![A_83, B_84, C_85]: (r1_tarski(k4_xboole_0(A_83, B_84), C_85) | ~r1_tarski(A_83, k2_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.51/3.11  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.51/3.11  tff(c_11292, plain, (![A_239, B_240, C_241]: (k2_xboole_0(k4_xboole_0(A_239, B_240), C_241)=C_241 | ~r1_tarski(A_239, k2_xboole_0(B_240, C_241)))), inference(resolution, [status(thm)], [c_1182, c_14])).
% 8.51/3.11  tff(c_11490, plain, (k2_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_131, c_11292])).
% 8.51/3.11  tff(c_618, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), A_69))), inference(superposition, [status(thm), theory('equality')], [c_530, c_34])).
% 8.51/3.11  tff(c_1690, plain, (![A_97, B_98]: (k2_xboole_0(k3_xboole_0(A_97, B_98), A_97)=A_97)), inference(resolution, [status(thm)], [c_618, c_14])).
% 8.51/3.11  tff(c_403, plain, (![A_62]: (k2_xboole_0(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_375])).
% 8.51/3.11  tff(c_2153, plain, (![B_104]: (k3_xboole_0(k1_xboole_0, B_104)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1690, c_403])).
% 8.51/3.11  tff(c_2202, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2153])).
% 8.51/3.11  tff(c_757, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.51/3.11  tff(c_799, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_757])).
% 8.51/3.11  tff(c_2268, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_799])).
% 8.51/3.11  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/3.11  tff(c_1384, plain, (![A_92, B_93, C_94]: (k2_xboole_0(k2_xboole_0(A_92, B_93), C_94)=k2_xboole_0(A_92, k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.51/3.11  tff(c_3968, plain, (![A_148, C_149]: (k2_xboole_0(A_148, k2_xboole_0(A_148, C_149))=k2_xboole_0(A_148, C_149))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1384])).
% 8.51/3.11  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.51/3.11  tff(c_3998, plain, (![A_148, C_149]: (k4_xboole_0(k2_xboole_0(A_148, C_149), k2_xboole_0(A_148, C_149))=k4_xboole_0(A_148, k2_xboole_0(A_148, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_3968, c_20])).
% 8.51/3.11  tff(c_6321, plain, (![A_178, C_179]: (k4_xboole_0(A_178, k2_xboole_0(A_178, C_179))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2268, c_3998])).
% 8.51/3.11  tff(c_572, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_530])).
% 8.51/3.11  tff(c_6344, plain, (![A_178, C_179]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(A_178, C_179), A_178), k1_xboole_0)=A_178)), inference(superposition, [status(thm), theory('equality')], [c_6321, c_572])).
% 8.51/3.11  tff(c_6450, plain, (![A_178, C_179]: (k3_xboole_0(A_178, k2_xboole_0(A_178, C_179))=A_178)), inference(demodulation, [status(thm), theory('equality')], [c_440, c_2, c_4, c_6344])).
% 8.51/3.11  tff(c_11705, plain, (k3_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11490, c_6450])).
% 8.51/3.11  tff(c_11756, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_11705])).
% 8.51/3.11  tff(c_30, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.51/3.11  tff(c_12006, plain, (k2_xboole_0(k3_xboole_0('#skF_5', '#skF_4'), k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_11756, c_30])).
% 8.51/3.11  tff(c_12026, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_440, c_2, c_4, c_12006])).
% 8.51/3.11  tff(c_640, plain, (![A_69, B_70]: (k2_xboole_0(k3_xboole_0(A_69, B_70), A_69)=A_69)), inference(resolution, [status(thm)], [c_618, c_14])).
% 8.51/3.11  tff(c_12361, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12026, c_640])).
% 8.51/3.11  tff(c_38, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.51/3.11  tff(c_240, plain, (![A_57, B_58]: (~r1_xboole_0(A_57, B_58) | k3_xboole_0(A_57, B_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_228])).
% 8.51/3.11  tff(c_247, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_240])).
% 8.51/3.11  tff(c_265, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_247])).
% 8.51/3.11  tff(c_24, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.51/3.11  tff(c_336, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_265, c_24])).
% 8.51/3.11  tff(c_339, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_336])).
% 8.51/3.11  tff(c_16, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.51/3.11  tff(c_12009, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11756, c_16])).
% 8.51/3.11  tff(c_12027, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_12009])).
% 8.51/3.11  tff(c_387, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_43, c_365])).
% 8.51/3.11  tff(c_1480, plain, (![A_5, C_94]: (k2_xboole_0(A_5, k2_xboole_0(A_5, C_94))=k2_xboole_0(A_5, C_94))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1384])).
% 8.51/3.11  tff(c_12600, plain, (![A_243, B_244, C_245]: (k4_xboole_0(k2_xboole_0(A_243, k2_xboole_0(B_244, C_245)), C_245)=k4_xboole_0(k2_xboole_0(A_243, B_244), C_245))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_20])).
% 8.51/3.11  tff(c_12859, plain, (![A_246]: (k4_xboole_0(k2_xboole_0(A_246, k2_xboole_0('#skF_4', '#skF_3')), '#skF_6')=k4_xboole_0(k2_xboole_0(A_246, '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_12600])).
% 8.51/3.11  tff(c_12931, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_6')=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1480, c_12859])).
% 8.51/3.11  tff(c_12981, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_12027, c_387, c_12931])).
% 8.51/3.11  tff(c_645, plain, (![A_71, B_72]: (r1_tarski(k4_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_530, c_82])).
% 8.51/3.11  tff(c_4599, plain, (![A_156, B_157]: (k2_xboole_0(k4_xboole_0(A_156, B_157), A_156)=A_156)), inference(resolution, [status(thm)], [c_645, c_14])).
% 8.51/3.11  tff(c_4687, plain, (![A_1, B_157]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_157))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4599])).
% 8.51/3.11  tff(c_13008, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_12981, c_4687])).
% 8.51/3.11  tff(c_13045, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12361, c_13008])).
% 8.51/3.11  tff(c_13047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_13045])).
% 8.51/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.11  
% 8.51/3.11  Inference rules
% 8.51/3.11  ----------------------
% 8.51/3.11  #Ref     : 0
% 8.51/3.11  #Sup     : 3279
% 8.51/3.11  #Fact    : 0
% 8.51/3.11  #Define  : 0
% 8.51/3.11  #Split   : 4
% 8.51/3.11  #Chain   : 0
% 8.51/3.11  #Close   : 0
% 8.51/3.11  
% 8.51/3.11  Ordering : KBO
% 8.51/3.11  
% 8.51/3.11  Simplification rules
% 8.51/3.11  ----------------------
% 8.51/3.11  #Subsume      : 108
% 8.51/3.11  #Demod        : 2924
% 8.51/3.11  #Tautology    : 2083
% 8.51/3.11  #SimpNegUnit  : 44
% 8.51/3.11  #BackRed      : 10
% 8.51/3.11  
% 8.51/3.11  #Partial instantiations: 0
% 8.51/3.11  #Strategies tried      : 1
% 8.51/3.11  
% 8.51/3.11  Timing (in seconds)
% 8.51/3.11  ----------------------
% 8.51/3.11  Preprocessing        : 0.33
% 8.51/3.11  Parsing              : 0.18
% 8.51/3.11  CNF conversion       : 0.02
% 8.51/3.11  Main loop            : 1.94
% 8.51/3.11  Inferencing          : 0.46
% 8.51/3.11  Reduction            : 1.01
% 8.51/3.12  Demodulation         : 0.86
% 8.51/3.12  BG Simplification    : 0.05
% 8.51/3.12  Subsumption          : 0.30
% 8.51/3.12  Abstraction          : 0.07
% 8.51/3.12  MUC search           : 0.00
% 8.51/3.12  Cooper               : 0.00
% 8.51/3.12  Total                : 2.31
% 8.51/3.12  Index Insertion      : 0.00
% 8.51/3.12  Index Deletion       : 0.00
% 8.51/3.12  Index Matching       : 0.00
% 8.51/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
