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
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   40 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 173 expanded)
%              Number of equality atoms :   41 (  64 expanded)
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

tff(f_112,negated_conjecture,(
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

tff(f_107,axiom,(
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

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

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

tff(c_196,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,(
    ! [A_27] : k3_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_196])).

tff(c_259,plain,(
    ! [D_82,B_83,A_84] :
      ( r2_hidden(D_82,B_83)
      | ~ r2_hidden(D_82,k3_xboole_0(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_273,plain,(
    ! [D_87,A_88] :
      ( r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_259])).

tff(c_277,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_88)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_273])).

tff(c_312,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_278,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_4'(A_89,B_90),A_89)
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_295,plain,(
    ! [A_91,B_92] :
      ( ~ v1_xboole_0(A_91)
      | r1_xboole_0(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_278,c_4])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_301,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,B_92) = A_91
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_295,c_52])).

tff(c_315,plain,(
    ! [B_92] : k4_xboole_0(k1_xboole_0,B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_312,c_301])).

tff(c_56,plain,(
    ! [B_35,A_34] : k2_tarski(B_35,A_34) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_148,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_409,plain,(
    ! [A_106,B_107] : k3_tarski(k2_tarski(A_106,B_107)) = k2_xboole_0(B_107,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_148])).

tff(c_70,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_436,plain,(
    ! [B_108,A_109] : k2_xboole_0(B_108,A_109) = k2_xboole_0(A_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_70])).

tff(c_489,plain,(
    ! [A_110] : k2_xboole_0(k1_xboole_0,A_110) = A_110 ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_42])).

tff(c_50,plain,(
    ! [A_30,B_31] : k4_xboole_0(k2_xboole_0(A_30,B_31),B_31) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_501,plain,(
    ! [A_110] : k4_xboole_0(k1_xboole_0,A_110) = k4_xboole_0(A_110,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_50])).

tff(c_524,plain,(
    ! [A_110] : k4_xboole_0(A_110,A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_501])).

tff(c_38,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_204,plain,(
    ! [B_21] : k3_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_38,c_196])).

tff(c_372,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_381,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_372])).

tff(c_567,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_381])).

tff(c_236,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tarski(A_77),B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2616,plain,(
    ! [A_208,B_209] :
      ( k3_xboole_0(k1_tarski(A_208),B_209) = k1_tarski(A_208)
      | ~ r2_hidden(A_208,B_209) ) ),
    inference(resolution,[status(thm)],[c_236,c_44])).

tff(c_40,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2628,plain,(
    ! [A_208,B_209] :
      ( k5_xboole_0(k1_tarski(A_208),k1_tarski(A_208)) = k4_xboole_0(k1_tarski(A_208),B_209)
      | ~ r2_hidden(A_208,B_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2616,c_40])).

tff(c_2652,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(k1_tarski(A_210),B_211) = k1_xboole_0
      | ~ r2_hidden(A_210,B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_2628])).

tff(c_48,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2697,plain,(
    ! [B_211,A_210] :
      ( k2_xboole_0(B_211,k1_tarski(A_210)) = k2_xboole_0(B_211,k1_xboole_0)
      | ~ r2_hidden(A_210,B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2652,c_48])).

tff(c_2752,plain,(
    ! [B_212,A_213] :
      ( k2_xboole_0(B_212,k1_tarski(A_213)) = B_212
      | ~ r2_hidden(A_213,B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2697])).

tff(c_415,plain,(
    ! [B_107,A_106] : k2_xboole_0(B_107,A_106) = k2_xboole_0(A_106,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_70])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_435,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_72])).

tff(c_2812,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2752,c_435])).

tff(c_2875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2812])).

tff(c_2894,plain,(
    ! [A_216] : r2_hidden('#skF_1'(k1_xboole_0),A_216) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_2917,plain,(
    ! [A_216] : ~ v1_xboole_0(A_216) ),
    inference(resolution,[status(thm)],[c_2894,c_4])).

tff(c_138,plain,(
    ! [A_60] :
      ( v1_xboole_0(A_60)
      | r2_hidden('#skF_1'(A_60),A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_144,plain,(
    ! [A_60] :
      ( ~ r2_hidden(A_60,'#skF_1'(A_60))
      | v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_2915,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2894,c_144])).

tff(c_2921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_2915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.67  
% 3.93/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.93/1.67  
% 3.93/1.67  %Foreground sorts:
% 3.93/1.67  
% 3.93/1.67  
% 3.93/1.67  %Background operators:
% 3.93/1.67  
% 3.93/1.67  
% 3.93/1.67  %Foreground operators:
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.93/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.93/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.93/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.93/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.93/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.93/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.93/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.93/1.67  
% 4.07/1.69  tff(f_112, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.07/1.69  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.07/1.69  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.07/1.69  tff(f_83, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.07/1.69  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.07/1.69  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.07/1.69  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.07/1.69  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.07/1.69  tff(f_93, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.07/1.69  tff(f_107, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.07/1.69  tff(f_87, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.07/1.69  tff(f_73, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.07/1.69  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.07/1.69  tff(f_105, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.07/1.69  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.07/1.69  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.07/1.69  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.07/1.69  tff(c_42, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.69  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.07/1.69  tff(c_46, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.07/1.69  tff(c_196, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.07/1.69  tff(c_203, plain, (![A_27]: (k3_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_196])).
% 4.07/1.69  tff(c_259, plain, (![D_82, B_83, A_84]: (r2_hidden(D_82, B_83) | ~r2_hidden(D_82, k3_xboole_0(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.07/1.69  tff(c_273, plain, (![D_87, A_88]: (r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_259])).
% 4.07/1.69  tff(c_277, plain, (![A_88]: (r2_hidden('#skF_1'(k1_xboole_0), A_88) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_273])).
% 4.07/1.69  tff(c_312, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_277])).
% 4.07/1.69  tff(c_278, plain, (![A_89, B_90]: (r2_hidden('#skF_4'(A_89, B_90), A_89) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.07/1.69  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.07/1.69  tff(c_295, plain, (![A_91, B_92]: (~v1_xboole_0(A_91) | r1_xboole_0(A_91, B_92))), inference(resolution, [status(thm)], [c_278, c_4])).
% 4.07/1.69  tff(c_52, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.07/1.69  tff(c_301, plain, (![A_91, B_92]: (k4_xboole_0(A_91, B_92)=A_91 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_295, c_52])).
% 4.07/1.69  tff(c_315, plain, (![B_92]: (k4_xboole_0(k1_xboole_0, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_312, c_301])).
% 4.07/1.69  tff(c_56, plain, (![B_35, A_34]: (k2_tarski(B_35, A_34)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.07/1.69  tff(c_148, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.07/1.69  tff(c_409, plain, (![A_106, B_107]: (k3_tarski(k2_tarski(A_106, B_107))=k2_xboole_0(B_107, A_106))), inference(superposition, [status(thm), theory('equality')], [c_56, c_148])).
% 4.07/1.69  tff(c_70, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.07/1.69  tff(c_436, plain, (![B_108, A_109]: (k2_xboole_0(B_108, A_109)=k2_xboole_0(A_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_409, c_70])).
% 4.07/1.69  tff(c_489, plain, (![A_110]: (k2_xboole_0(k1_xboole_0, A_110)=A_110)), inference(superposition, [status(thm), theory('equality')], [c_436, c_42])).
% 4.07/1.69  tff(c_50, plain, (![A_30, B_31]: (k4_xboole_0(k2_xboole_0(A_30, B_31), B_31)=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.07/1.69  tff(c_501, plain, (![A_110]: (k4_xboole_0(k1_xboole_0, A_110)=k4_xboole_0(A_110, A_110))), inference(superposition, [status(thm), theory('equality')], [c_489, c_50])).
% 4.07/1.69  tff(c_524, plain, (![A_110]: (k4_xboole_0(A_110, A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_501])).
% 4.07/1.69  tff(c_38, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.69  tff(c_204, plain, (![B_21]: (k3_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_38, c_196])).
% 4.07/1.69  tff(c_372, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.07/1.69  tff(c_381, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_204, c_372])).
% 4.07/1.69  tff(c_567, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_381])).
% 4.07/1.69  tff(c_236, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), B_78) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.07/1.69  tff(c_44, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.07/1.69  tff(c_2616, plain, (![A_208, B_209]: (k3_xboole_0(k1_tarski(A_208), B_209)=k1_tarski(A_208) | ~r2_hidden(A_208, B_209))), inference(resolution, [status(thm)], [c_236, c_44])).
% 4.07/1.69  tff(c_40, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.07/1.69  tff(c_2628, plain, (![A_208, B_209]: (k5_xboole_0(k1_tarski(A_208), k1_tarski(A_208))=k4_xboole_0(k1_tarski(A_208), B_209) | ~r2_hidden(A_208, B_209))), inference(superposition, [status(thm), theory('equality')], [c_2616, c_40])).
% 4.07/1.69  tff(c_2652, plain, (![A_210, B_211]: (k4_xboole_0(k1_tarski(A_210), B_211)=k1_xboole_0 | ~r2_hidden(A_210, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_2628])).
% 4.07/1.69  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.07/1.69  tff(c_2697, plain, (![B_211, A_210]: (k2_xboole_0(B_211, k1_tarski(A_210))=k2_xboole_0(B_211, k1_xboole_0) | ~r2_hidden(A_210, B_211))), inference(superposition, [status(thm), theory('equality')], [c_2652, c_48])).
% 4.07/1.69  tff(c_2752, plain, (![B_212, A_213]: (k2_xboole_0(B_212, k1_tarski(A_213))=B_212 | ~r2_hidden(A_213, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2697])).
% 4.07/1.69  tff(c_415, plain, (![B_107, A_106]: (k2_xboole_0(B_107, A_106)=k2_xboole_0(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_409, c_70])).
% 4.07/1.69  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.07/1.69  tff(c_435, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_72])).
% 4.07/1.69  tff(c_2812, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2752, c_435])).
% 4.07/1.69  tff(c_2875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2812])).
% 4.07/1.69  tff(c_2894, plain, (![A_216]: (r2_hidden('#skF_1'(k1_xboole_0), A_216))), inference(splitRight, [status(thm)], [c_277])).
% 4.07/1.69  tff(c_2917, plain, (![A_216]: (~v1_xboole_0(A_216))), inference(resolution, [status(thm)], [c_2894, c_4])).
% 4.07/1.69  tff(c_138, plain, (![A_60]: (v1_xboole_0(A_60) | r2_hidden('#skF_1'(A_60), A_60))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.07/1.69  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.07/1.69  tff(c_144, plain, (![A_60]: (~r2_hidden(A_60, '#skF_1'(A_60)) | v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_138, c_2])).
% 4.07/1.69  tff(c_2915, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_2894, c_144])).
% 4.07/1.69  tff(c_2921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2917, c_2915])).
% 4.07/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.69  
% 4.07/1.69  Inference rules
% 4.07/1.69  ----------------------
% 4.07/1.69  #Ref     : 0
% 4.07/1.69  #Sup     : 677
% 4.07/1.69  #Fact    : 0
% 4.07/1.69  #Define  : 0
% 4.07/1.69  #Split   : 1
% 4.07/1.69  #Chain   : 0
% 4.07/1.69  #Close   : 0
% 4.07/1.69  
% 4.07/1.69  Ordering : KBO
% 4.07/1.69  
% 4.07/1.69  Simplification rules
% 4.07/1.69  ----------------------
% 4.07/1.69  #Subsume      : 58
% 4.07/1.69  #Demod        : 555
% 4.07/1.69  #Tautology    : 461
% 4.07/1.69  #SimpNegUnit  : 5
% 4.07/1.69  #BackRed      : 5
% 4.07/1.69  
% 4.07/1.69  #Partial instantiations: 0
% 4.07/1.69  #Strategies tried      : 1
% 4.07/1.69  
% 4.07/1.69  Timing (in seconds)
% 4.07/1.69  ----------------------
% 4.07/1.69  Preprocessing        : 0.33
% 4.07/1.69  Parsing              : 0.17
% 4.07/1.69  CNF conversion       : 0.02
% 4.07/1.69  Main loop            : 0.59
% 4.07/1.69  Inferencing          : 0.20
% 4.07/1.69  Reduction            : 0.23
% 4.07/1.69  Demodulation         : 0.18
% 4.07/1.69  BG Simplification    : 0.02
% 4.07/1.69  Subsumption          : 0.10
% 4.07/1.69  Abstraction          : 0.03
% 4.07/1.69  MUC search           : 0.00
% 4.07/1.69  Cooper               : 0.00
% 4.07/1.69  Total                : 0.95
% 4.07/1.69  Index Insertion      : 0.00
% 4.07/1.69  Index Deletion       : 0.00
% 4.07/1.69  Index Matching       : 0.00
% 4.07/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
