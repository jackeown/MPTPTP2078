%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :   90 ( 155 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_72,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_174,plain,(
    ! [B_59,A_60] : k3_tarski(k2_tarski(B_59,A_60)) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_42,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_208,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_42])).

tff(c_224,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_22])).

tff(c_296,plain,(
    ! [A_66,B_67] : k2_xboole_0(A_66,k4_xboole_0(B_67,A_66)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_303,plain,(
    ! [B_67] : k4_xboole_0(B_67,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_224])).

tff(c_312,plain,(
    ! [B_67] : k4_xboole_0(B_67,k1_xboole_0) = B_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_303])).

tff(c_626,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(A_98,B_99),A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | ~ r1_xboole_0(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_110,plain,(
    ! [A_24] : r1_xboole_0(k1_xboole_0,A_24) ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_18,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_164,plain,(
    ! [B_14] : k3_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_537,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,k3_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_542,plain,(
    ! [B_89,C_90] :
      ( ~ r1_xboole_0(B_89,B_89)
      | ~ r2_hidden(C_90,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_537])).

tff(c_549,plain,(
    ! [C_90] : ~ r2_hidden(C_90,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_110,c_542])).

tff(c_644,plain,(
    ! [B_102] : r1_tarski(k1_xboole_0,B_102) ),
    inference(resolution,[status(thm)],[c_626,c_549])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_652,plain,(
    ! [B_103] : k3_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_644,c_24])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_690,plain,(
    ! [B_105] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_20])).

tff(c_315,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_324,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k4_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_315])).

tff(c_702,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_324])).

tff(c_716,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_702])).

tff(c_350,plain,(
    ! [A_72,B_73] : k4_xboole_0(k2_xboole_0(A_72,B_73),B_73) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_373,plain,(
    ! [A_64] : k4_xboole_0(k1_xboole_0,A_64) = k4_xboole_0(A_64,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_350])).

tff(c_722,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_373])).

tff(c_761,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_324])).

tff(c_34,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1250,plain,(
    ! [A_145,B_146,C_147] :
      ( r1_tarski(k2_tarski(A_145,B_146),C_147)
      | ~ r2_hidden(B_146,C_147)
      | ~ r2_hidden(A_145,C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1630,plain,(
    ! [A_159,C_160] :
      ( r1_tarski(k1_tarski(A_159),C_160)
      | ~ r2_hidden(A_159,C_160)
      | ~ r2_hidden(A_159,C_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1250])).

tff(c_2770,plain,(
    ! [A_184,C_185] :
      ( k3_xboole_0(k1_tarski(A_184),C_185) = k1_tarski(A_184)
      | ~ r2_hidden(A_184,C_185) ) ),
    inference(resolution,[status(thm)],[c_1630,c_24])).

tff(c_2792,plain,(
    ! [A_184,C_185] :
      ( k5_xboole_0(k1_tarski(A_184),k1_tarski(A_184)) = k4_xboole_0(k1_tarski(A_184),C_185)
      | ~ r2_hidden(A_184,C_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2770,c_20])).

tff(c_2817,plain,(
    ! [A_186,C_187] :
      ( k4_xboole_0(k1_tarski(A_186),C_187) = k1_xboole_0
      | ~ r2_hidden(A_186,C_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_2792])).

tff(c_26,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2851,plain,(
    ! [C_187,A_186] :
      ( k2_xboole_0(C_187,k1_tarski(A_186)) = k2_xboole_0(C_187,k1_xboole_0)
      | ~ r2_hidden(A_186,C_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2817,c_26])).

tff(c_2888,plain,(
    ! [C_188,A_189] :
      ( k2_xboole_0(C_188,k1_tarski(A_189)) = C_188
      | ~ r2_hidden(A_189,C_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2851])).

tff(c_180,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_42])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_207,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_50])).

tff(c_2965,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2888,c_207])).

tff(c_3033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.58  
% 3.67/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.67/1.58  
% 3.67/1.58  %Foreground sorts:
% 3.67/1.58  
% 3.67/1.58  
% 3.67/1.58  %Background operators:
% 3.67/1.58  
% 3.67/1.58  
% 3.67/1.58  %Foreground operators:
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.67/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.67/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.67/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.67/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.67/1.58  
% 3.67/1.60  tff(f_93, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.67/1.60  tff(f_60, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.67/1.60  tff(f_72, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.67/1.60  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.67/1.60  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.67/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.67/1.60  tff(f_70, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.67/1.60  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.67/1.60  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.67/1.60  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.67/1.60  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.67/1.60  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.67/1.60  tff(f_68, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.67/1.60  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.67/1.60  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.67/1.60  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.67/1.60  tff(c_22, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.67/1.60  tff(c_32, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.67/1.60  tff(c_125, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.67/1.60  tff(c_174, plain, (![B_59, A_60]: (k3_tarski(k2_tarski(B_59, A_60))=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_32, c_125])).
% 3.67/1.60  tff(c_42, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.67/1.60  tff(c_208, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_174, c_42])).
% 3.67/1.60  tff(c_224, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_208, c_22])).
% 3.67/1.60  tff(c_296, plain, (![A_66, B_67]: (k2_xboole_0(A_66, k4_xboole_0(B_67, A_66))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.67/1.60  tff(c_303, plain, (![B_67]: (k4_xboole_0(B_67, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_67))), inference(superposition, [status(thm), theory('equality')], [c_296, c_224])).
% 3.67/1.60  tff(c_312, plain, (![B_67]: (k4_xboole_0(B_67, k1_xboole_0)=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_303])).
% 3.67/1.60  tff(c_626, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(A_98, B_99), A_98) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.67/1.60  tff(c_30, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.67/1.60  tff(c_107, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | ~r1_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.60  tff(c_110, plain, (![A_24]: (r1_xboole_0(k1_xboole_0, A_24))), inference(resolution, [status(thm)], [c_30, c_107])).
% 3.67/1.60  tff(c_18, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.67/1.60  tff(c_160, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.67/1.60  tff(c_164, plain, (![B_14]: (k3_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_18, c_160])).
% 3.67/1.60  tff(c_537, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, k3_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.67/1.60  tff(c_542, plain, (![B_89, C_90]: (~r1_xboole_0(B_89, B_89) | ~r2_hidden(C_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_164, c_537])).
% 3.67/1.60  tff(c_549, plain, (![C_90]: (~r2_hidden(C_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_110, c_542])).
% 3.67/1.60  tff(c_644, plain, (![B_102]: (r1_tarski(k1_xboole_0, B_102))), inference(resolution, [status(thm)], [c_626, c_549])).
% 3.67/1.60  tff(c_24, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.67/1.60  tff(c_652, plain, (![B_103]: (k3_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_644, c_24])).
% 3.67/1.60  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.67/1.60  tff(c_690, plain, (![B_105]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_652, c_20])).
% 3.67/1.60  tff(c_315, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.67/1.60  tff(c_324, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k4_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_164, c_315])).
% 3.67/1.60  tff(c_702, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_690, c_324])).
% 3.67/1.60  tff(c_716, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_702])).
% 3.67/1.60  tff(c_350, plain, (![A_72, B_73]: (k4_xboole_0(k2_xboole_0(A_72, B_73), B_73)=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.67/1.60  tff(c_373, plain, (![A_64]: (k4_xboole_0(k1_xboole_0, A_64)=k4_xboole_0(A_64, A_64))), inference(superposition, [status(thm), theory('equality')], [c_224, c_350])).
% 3.67/1.60  tff(c_722, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_716, c_373])).
% 3.67/1.60  tff(c_761, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_722, c_324])).
% 3.67/1.60  tff(c_34, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.67/1.60  tff(c_1250, plain, (![A_145, B_146, C_147]: (r1_tarski(k2_tarski(A_145, B_146), C_147) | ~r2_hidden(B_146, C_147) | ~r2_hidden(A_145, C_147))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.67/1.60  tff(c_1630, plain, (![A_159, C_160]: (r1_tarski(k1_tarski(A_159), C_160) | ~r2_hidden(A_159, C_160) | ~r2_hidden(A_159, C_160))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1250])).
% 3.67/1.60  tff(c_2770, plain, (![A_184, C_185]: (k3_xboole_0(k1_tarski(A_184), C_185)=k1_tarski(A_184) | ~r2_hidden(A_184, C_185))), inference(resolution, [status(thm)], [c_1630, c_24])).
% 3.67/1.60  tff(c_2792, plain, (![A_184, C_185]: (k5_xboole_0(k1_tarski(A_184), k1_tarski(A_184))=k4_xboole_0(k1_tarski(A_184), C_185) | ~r2_hidden(A_184, C_185))), inference(superposition, [status(thm), theory('equality')], [c_2770, c_20])).
% 3.67/1.60  tff(c_2817, plain, (![A_186, C_187]: (k4_xboole_0(k1_tarski(A_186), C_187)=k1_xboole_0 | ~r2_hidden(A_186, C_187))), inference(demodulation, [status(thm), theory('equality')], [c_761, c_2792])).
% 3.67/1.60  tff(c_26, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.67/1.60  tff(c_2851, plain, (![C_187, A_186]: (k2_xboole_0(C_187, k1_tarski(A_186))=k2_xboole_0(C_187, k1_xboole_0) | ~r2_hidden(A_186, C_187))), inference(superposition, [status(thm), theory('equality')], [c_2817, c_26])).
% 3.67/1.60  tff(c_2888, plain, (![C_188, A_189]: (k2_xboole_0(C_188, k1_tarski(A_189))=C_188 | ~r2_hidden(A_189, C_188))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2851])).
% 3.67/1.60  tff(c_180, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_174, c_42])).
% 3.67/1.60  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.67/1.60  tff(c_207, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_50])).
% 3.67/1.60  tff(c_2965, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2888, c_207])).
% 3.67/1.60  tff(c_3033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_2965])).
% 3.67/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.60  
% 3.67/1.60  Inference rules
% 3.67/1.60  ----------------------
% 3.67/1.60  #Ref     : 0
% 3.67/1.60  #Sup     : 714
% 3.67/1.60  #Fact    : 0
% 3.67/1.60  #Define  : 0
% 3.67/1.60  #Split   : 0
% 3.67/1.60  #Chain   : 0
% 3.67/1.60  #Close   : 0
% 3.67/1.60  
% 3.67/1.60  Ordering : KBO
% 3.67/1.60  
% 3.67/1.60  Simplification rules
% 3.67/1.60  ----------------------
% 3.67/1.60  #Subsume      : 69
% 3.67/1.60  #Demod        : 780
% 3.67/1.60  #Tautology    : 519
% 3.67/1.60  #SimpNegUnit  : 2
% 3.67/1.60  #BackRed      : 7
% 3.67/1.60  
% 3.67/1.60  #Partial instantiations: 0
% 3.67/1.60  #Strategies tried      : 1
% 3.67/1.60  
% 3.67/1.60  Timing (in seconds)
% 3.67/1.60  ----------------------
% 3.67/1.60  Preprocessing        : 0.29
% 3.67/1.60  Parsing              : 0.15
% 3.67/1.60  CNF conversion       : 0.02
% 3.67/1.60  Main loop            : 0.58
% 3.67/1.60  Inferencing          : 0.19
% 3.67/1.60  Reduction            : 0.26
% 3.67/1.60  Demodulation         : 0.22
% 3.67/1.60  BG Simplification    : 0.02
% 3.67/1.60  Subsumption          : 0.08
% 3.67/1.60  Abstraction          : 0.03
% 3.67/1.60  MUC search           : 0.00
% 3.67/1.60  Cooper               : 0.00
% 3.67/1.60  Total                : 0.92
% 3.67/1.60  Index Insertion      : 0.00
% 3.67/1.60  Index Deletion       : 0.00
% 3.67/1.60  Index Matching       : 0.00
% 3.67/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
