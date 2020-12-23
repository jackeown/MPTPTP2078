%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 169 expanded)
%              Number of leaves         :   48 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :   90 ( 200 expanded)
%              Number of equality atoms :   39 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_80,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_4'),'#skF_5') != k10_relat_1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3566,plain,(
    ! [A_239,B_240,C_241] : k3_xboole_0(k3_xboole_0(A_239,B_240),C_241) = k3_xboole_0(A_239,k3_xboole_0(B_240,C_241)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_24,B_25] : r1_tarski(k3_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_215,plain,(
    ! [A_113,B_114] :
      ( k3_xboole_0(A_113,B_114) = A_113
      | ~ r1_tarski(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,(
    ! [A_24,B_25] : k3_xboole_0(k3_xboole_0(A_24,B_25),A_24) = k3_xboole_0(A_24,B_25) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_3610,plain,(
    ! [C_241,B_240] : k3_xboole_0(C_241,k3_xboole_0(B_240,C_241)) = k3_xboole_0(C_241,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_3566,c_240])).

tff(c_34,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,A_29) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_344,plain,(
    ! [A_120,B_121] :
      ( k2_xboole_0(A_120,B_121) = B_121
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_373,plain,(
    ! [A_122] : k2_xboole_0(k1_xboole_0,A_122) = A_122 ),
    inference(resolution,[status(thm)],[c_34,c_344])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_388,plain,(
    ! [A_122] : k2_xboole_0(A_122,k1_xboole_0) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_2])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] : k3_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k3_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2181,plain,(
    ! [A_202,B_203,C_204] : k4_xboole_0(k3_xboole_0(A_202,B_203),C_204) = k3_xboole_0(A_202,k4_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    ! [A_37,B_38] : r1_xboole_0(k4_xboole_0(A_37,B_38),B_38) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2271,plain,(
    ! [A_205,B_206,C_207] : r1_xboole_0(k3_xboole_0(A_205,k4_xboole_0(B_206,C_207)),C_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_2181,c_42])).

tff(c_2350,plain,(
    ! [B_211,C_212,B_213] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_211,C_212),B_213),C_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2271])).

tff(c_995,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_1'(A_152,B_153),A_152)
      | r1_tarski(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1591,plain,(
    ! [A_178,B_179,B_180] :
      ( ~ r1_xboole_0(A_178,B_179)
      | r1_tarski(k3_xboole_0(A_178,B_179),B_180) ) ),
    inference(resolution,[status(thm)],[c_995,c_14])).

tff(c_862,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_882,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_862])).

tff(c_1628,plain,(
    ! [A_178,B_179] :
      ( k3_xboole_0(A_178,B_179) = k1_xboole_0
      | ~ r1_xboole_0(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_1591,c_882])).

tff(c_7481,plain,(
    ! [B_331,C_332,B_333] : k3_xboole_0(k3_xboole_0(k4_xboole_0(B_331,C_332),B_333),C_332) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2350,c_1628])).

tff(c_8517,plain,(
    ! [B_347,C_348,B_349] : k3_xboole_0(k4_xboole_0(B_347,C_348),k3_xboole_0(B_349,C_348)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7481])).

tff(c_36,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_239,plain,(
    ! [A_30,B_31] : k3_xboole_0(k4_xboole_0(A_30,B_31),A_30) = k4_xboole_0(A_30,B_31) ),
    inference(resolution,[status(thm)],[c_36,c_215])).

tff(c_8790,plain,(
    ! [B_350,C_351] : k4_xboole_0(k3_xboole_0(B_350,C_351),C_351) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8517,c_239])).

tff(c_38,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8919,plain,(
    ! [C_351,B_350] : k2_xboole_0(C_351,k3_xboole_0(B_350,C_351)) = k2_xboole_0(C_351,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8790,c_38])).

tff(c_9238,plain,(
    ! [C_352,B_353] : k2_xboole_0(C_352,k3_xboole_0(B_353,C_352)) = C_352 ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_8919])).

tff(c_148,plain,(
    ! [B_105,A_106] : k2_xboole_0(B_105,A_106) = k2_xboole_0(A_106,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_39,B_40] : r1_tarski(A_39,k2_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_163,plain,(
    ! [A_106,B_105] : r1_tarski(A_106,k2_xboole_0(B_105,A_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_44])).

tff(c_9437,plain,(
    ! [B_354,C_355] : r1_tarski(k3_xboole_0(B_354,C_355),C_355) ),
    inference(superposition,[status(thm),theory(equality)],[c_9238,c_163])).

tff(c_9470,plain,(
    ! [C_241,B_240] : r1_tarski(k3_xboole_0(C_241,B_240),k3_xboole_0(B_240,C_241)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3610,c_9437])).

tff(c_9773,plain,(
    ! [C_365,B_366] : r1_tarski(k3_xboole_0(C_365,B_366),k3_xboole_0(B_366,C_365)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3610,c_9437])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9775,plain,(
    ! [C_365,B_366] :
      ( k3_xboole_0(C_365,B_366) = k3_xboole_0(B_366,C_365)
      | ~ r1_tarski(k3_xboole_0(B_366,C_365),k3_xboole_0(C_365,B_366)) ) ),
    inference(resolution,[status(thm)],[c_9773,c_16])).

tff(c_9959,plain,(
    ! [C_367,B_368] : k3_xboole_0(C_367,B_368) = k3_xboole_0(B_368,C_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9470,c_9775])).

tff(c_82,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_241,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_5'),'#skF_4') = k10_relat_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_215])).

tff(c_10281,plain,(
    k3_xboole_0('#skF_4',k10_relat_1('#skF_3','#skF_5')) = k10_relat_1('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9959,c_241])).

tff(c_76,plain,(
    ! [A_82,C_84,B_83] :
      ( k3_xboole_0(A_82,k10_relat_1(C_84,B_83)) = k10_relat_1(k7_relat_1(C_84,A_82),B_83)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13175,plain,
    ( k10_relat_1(k7_relat_1('#skF_3','#skF_4'),'#skF_5') = k10_relat_1('#skF_3','#skF_5')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10281,c_76])).

tff(c_13249,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_4'),'#skF_5') = k10_relat_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_13175])).

tff(c_13251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_13249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.53  
% 6.87/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.87/2.53  
% 6.87/2.53  %Foreground sorts:
% 6.87/2.53  
% 6.87/2.53  
% 6.87/2.53  %Background operators:
% 6.87/2.53  
% 6.87/2.53  
% 6.87/2.53  %Foreground operators:
% 6.87/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.87/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.87/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.87/2.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.87/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.87/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.87/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.87/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.87/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.87/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.87/2.53  tff('#skF_5', type, '#skF_5': $i).
% 6.87/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.87/2.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.87/2.53  tff('#skF_3', type, '#skF_3': $i).
% 6.87/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.87/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.87/2.53  tff('#skF_4', type, '#skF_4': $i).
% 6.87/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.87/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.87/2.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.87/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.87/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.87/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.87/2.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.87/2.53  
% 6.87/2.54  tff(f_143, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 6.87/2.54  tff(f_64, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.87/2.54  tff(f_66, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.87/2.54  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.87/2.54  tff(f_74, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.87/2.54  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.87/2.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.87/2.54  tff(f_80, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.87/2.54  tff(f_82, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.87/2.54  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.87/2.54  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.87/2.54  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.87/2.54  tff(f_76, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.87/2.54  tff(f_78, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.87/2.54  tff(f_84, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.87/2.54  tff(f_131, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.87/2.54  tff(c_80, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_4'), '#skF_5')!=k10_relat_1('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.87/2.54  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.87/2.54  tff(c_3566, plain, (![A_239, B_240, C_241]: (k3_xboole_0(k3_xboole_0(A_239, B_240), C_241)=k3_xboole_0(A_239, k3_xboole_0(B_240, C_241)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.87/2.54  tff(c_28, plain, (![A_24, B_25]: (r1_tarski(k3_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.87/2.54  tff(c_215, plain, (![A_113, B_114]: (k3_xboole_0(A_113, B_114)=A_113 | ~r1_tarski(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.87/2.54  tff(c_240, plain, (![A_24, B_25]: (k3_xboole_0(k3_xboole_0(A_24, B_25), A_24)=k3_xboole_0(A_24, B_25))), inference(resolution, [status(thm)], [c_28, c_215])).
% 6.87/2.54  tff(c_3610, plain, (![C_241, B_240]: (k3_xboole_0(C_241, k3_xboole_0(B_240, C_241))=k3_xboole_0(C_241, B_240))), inference(superposition, [status(thm), theory('equality')], [c_3566, c_240])).
% 6.87/2.54  tff(c_34, plain, (![A_29]: (r1_tarski(k1_xboole_0, A_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.87/2.54  tff(c_344, plain, (![A_120, B_121]: (k2_xboole_0(A_120, B_121)=B_121 | ~r1_tarski(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.87/2.54  tff(c_373, plain, (![A_122]: (k2_xboole_0(k1_xboole_0, A_122)=A_122)), inference(resolution, [status(thm)], [c_34, c_344])).
% 6.87/2.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.87/2.54  tff(c_388, plain, (![A_122]: (k2_xboole_0(A_122, k1_xboole_0)=A_122)), inference(superposition, [status(thm), theory('equality')], [c_373, c_2])).
% 6.87/2.54  tff(c_26, plain, (![A_21, B_22, C_23]: (k3_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k3_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.87/2.54  tff(c_2181, plain, (![A_202, B_203, C_204]: (k4_xboole_0(k3_xboole_0(A_202, B_203), C_204)=k3_xboole_0(A_202, k4_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.87/2.54  tff(c_42, plain, (![A_37, B_38]: (r1_xboole_0(k4_xboole_0(A_37, B_38), B_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.87/2.54  tff(c_2271, plain, (![A_205, B_206, C_207]: (r1_xboole_0(k3_xboole_0(A_205, k4_xboole_0(B_206, C_207)), C_207))), inference(superposition, [status(thm), theory('equality')], [c_2181, c_42])).
% 6.87/2.54  tff(c_2350, plain, (![B_211, C_212, B_213]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_211, C_212), B_213), C_212))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2271])).
% 6.87/2.54  tff(c_995, plain, (![A_152, B_153]: (r2_hidden('#skF_1'(A_152, B_153), A_152) | r1_tarski(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.87/2.54  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.87/2.54  tff(c_1591, plain, (![A_178, B_179, B_180]: (~r1_xboole_0(A_178, B_179) | r1_tarski(k3_xboole_0(A_178, B_179), B_180))), inference(resolution, [status(thm)], [c_995, c_14])).
% 6.87/2.54  tff(c_862, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.87/2.54  tff(c_882, plain, (![A_29]: (k1_xboole_0=A_29 | ~r1_tarski(A_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_862])).
% 6.87/2.54  tff(c_1628, plain, (![A_178, B_179]: (k3_xboole_0(A_178, B_179)=k1_xboole_0 | ~r1_xboole_0(A_178, B_179))), inference(resolution, [status(thm)], [c_1591, c_882])).
% 6.87/2.54  tff(c_7481, plain, (![B_331, C_332, B_333]: (k3_xboole_0(k3_xboole_0(k4_xboole_0(B_331, C_332), B_333), C_332)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2350, c_1628])).
% 6.87/2.54  tff(c_8517, plain, (![B_347, C_348, B_349]: (k3_xboole_0(k4_xboole_0(B_347, C_348), k3_xboole_0(B_349, C_348))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_7481])).
% 6.87/2.54  tff(c_36, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.87/2.54  tff(c_239, plain, (![A_30, B_31]: (k3_xboole_0(k4_xboole_0(A_30, B_31), A_30)=k4_xboole_0(A_30, B_31))), inference(resolution, [status(thm)], [c_36, c_215])).
% 6.87/2.54  tff(c_8790, plain, (![B_350, C_351]: (k4_xboole_0(k3_xboole_0(B_350, C_351), C_351)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8517, c_239])).
% 6.87/2.54  tff(c_38, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.87/2.54  tff(c_8919, plain, (![C_351, B_350]: (k2_xboole_0(C_351, k3_xboole_0(B_350, C_351))=k2_xboole_0(C_351, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8790, c_38])).
% 6.87/2.54  tff(c_9238, plain, (![C_352, B_353]: (k2_xboole_0(C_352, k3_xboole_0(B_353, C_352))=C_352)), inference(demodulation, [status(thm), theory('equality')], [c_388, c_8919])).
% 6.87/2.54  tff(c_148, plain, (![B_105, A_106]: (k2_xboole_0(B_105, A_106)=k2_xboole_0(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.87/2.54  tff(c_44, plain, (![A_39, B_40]: (r1_tarski(A_39, k2_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.87/2.54  tff(c_163, plain, (![A_106, B_105]: (r1_tarski(A_106, k2_xboole_0(B_105, A_106)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_44])).
% 6.87/2.54  tff(c_9437, plain, (![B_354, C_355]: (r1_tarski(k3_xboole_0(B_354, C_355), C_355))), inference(superposition, [status(thm), theory('equality')], [c_9238, c_163])).
% 6.87/2.54  tff(c_9470, plain, (![C_241, B_240]: (r1_tarski(k3_xboole_0(C_241, B_240), k3_xboole_0(B_240, C_241)))), inference(superposition, [status(thm), theory('equality')], [c_3610, c_9437])).
% 6.87/2.54  tff(c_9773, plain, (![C_365, B_366]: (r1_tarski(k3_xboole_0(C_365, B_366), k3_xboole_0(B_366, C_365)))), inference(superposition, [status(thm), theory('equality')], [c_3610, c_9437])).
% 6.87/2.54  tff(c_16, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.87/2.54  tff(c_9775, plain, (![C_365, B_366]: (k3_xboole_0(C_365, B_366)=k3_xboole_0(B_366, C_365) | ~r1_tarski(k3_xboole_0(B_366, C_365), k3_xboole_0(C_365, B_366)))), inference(resolution, [status(thm)], [c_9773, c_16])).
% 6.87/2.54  tff(c_9959, plain, (![C_367, B_368]: (k3_xboole_0(C_367, B_368)=k3_xboole_0(B_368, C_367))), inference(demodulation, [status(thm), theory('equality')], [c_9470, c_9775])).
% 6.87/2.54  tff(c_82, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.87/2.54  tff(c_241, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_5'), '#skF_4')=k10_relat_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_215])).
% 6.87/2.54  tff(c_10281, plain, (k3_xboole_0('#skF_4', k10_relat_1('#skF_3', '#skF_5'))=k10_relat_1('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9959, c_241])).
% 6.87/2.54  tff(c_76, plain, (![A_82, C_84, B_83]: (k3_xboole_0(A_82, k10_relat_1(C_84, B_83))=k10_relat_1(k7_relat_1(C_84, A_82), B_83) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.87/2.54  tff(c_13175, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_4'), '#skF_5')=k10_relat_1('#skF_3', '#skF_5') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10281, c_76])).
% 6.87/2.54  tff(c_13249, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_4'), '#skF_5')=k10_relat_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_13175])).
% 6.87/2.54  tff(c_13251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_13249])).
% 6.87/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.54  
% 6.87/2.54  Inference rules
% 6.87/2.54  ----------------------
% 6.87/2.54  #Ref     : 0
% 6.87/2.54  #Sup     : 3347
% 6.87/2.54  #Fact    : 0
% 6.87/2.54  #Define  : 0
% 6.87/2.54  #Split   : 2
% 6.87/2.54  #Chain   : 0
% 6.87/2.54  #Close   : 0
% 6.87/2.54  
% 6.87/2.54  Ordering : KBO
% 6.87/2.54  
% 6.87/2.54  Simplification rules
% 6.87/2.54  ----------------------
% 6.87/2.54  #Subsume      : 83
% 6.87/2.54  #Demod        : 2943
% 6.87/2.54  #Tautology    : 2322
% 6.87/2.54  #SimpNegUnit  : 12
% 6.87/2.55  #BackRed      : 7
% 6.87/2.55  
% 6.87/2.55  #Partial instantiations: 0
% 6.87/2.55  #Strategies tried      : 1
% 6.87/2.55  
% 6.87/2.55  Timing (in seconds)
% 6.87/2.55  ----------------------
% 6.87/2.55  Preprocessing        : 0.35
% 6.87/2.55  Parsing              : 0.19
% 6.87/2.55  CNF conversion       : 0.02
% 6.87/2.55  Main loop            : 1.44
% 6.87/2.55  Inferencing          : 0.37
% 6.87/2.55  Reduction            : 0.70
% 6.87/2.55  Demodulation         : 0.58
% 6.87/2.55  BG Simplification    : 0.05
% 6.87/2.55  Subsumption          : 0.24
% 6.87/2.55  Abstraction          : 0.06
% 6.87/2.55  MUC search           : 0.00
% 6.87/2.55  Cooper               : 0.00
% 6.87/2.55  Total                : 1.82
% 6.87/2.55  Index Insertion      : 0.00
% 6.87/2.55  Index Deletion       : 0.00
% 6.87/2.55  Index Matching       : 0.00
% 6.87/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
