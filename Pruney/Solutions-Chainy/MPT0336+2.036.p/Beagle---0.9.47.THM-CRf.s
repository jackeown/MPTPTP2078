%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 307 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 724 expanded)
%              Number of equality atoms :   14 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_141,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_162,plain,(
    ! [A_59,B_60,A_10] :
      ( ~ r1_xboole_0(A_59,B_60)
      | r1_xboole_0(A_10,k3_xboole_0(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_14,c_141])).

tff(c_50,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | ~ r1_xboole_0(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_479,plain,(
    ! [A_121,C_122,B_123] :
      ( ~ r1_xboole_0(A_121,C_122)
      | ~ r1_xboole_0(A_121,B_123)
      | r1_xboole_0(A_121,k2_xboole_0(B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1263,plain,(
    ! [B_223,C_224,A_225] :
      ( r1_xboole_0(k2_xboole_0(B_223,C_224),A_225)
      | ~ r1_xboole_0(A_225,C_224)
      | ~ r1_xboole_0(A_225,B_223) ) ),
    inference(resolution,[status(thm)],[c_479,c_10])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1286,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_8')
    | ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1263,c_48])).

tff(c_1297,plain,(
    ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1286])).

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_251,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_964,plain,(
    ! [A_191,B_192,B_193] :
      ( r2_hidden('#skF_2'(A_191,B_192),B_193)
      | ~ r1_tarski(B_192,B_193)
      | r1_xboole_0(A_191,B_192) ) ),
    inference(resolution,[status(thm)],[c_14,c_251])).

tff(c_30,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3025,plain,(
    ! [A_368,A_369,B_370] :
      ( A_368 = '#skF_2'(A_369,B_370)
      | ~ r1_tarski(B_370,k1_tarski(A_368))
      | r1_xboole_0(A_369,B_370) ) ),
    inference(resolution,[status(thm)],[c_964,c_30])).

tff(c_3146,plain,(
    ! [A_374] :
      ( '#skF_2'(A_374,k3_xboole_0('#skF_6','#skF_7')) = '#skF_9'
      | r1_xboole_0(A_374,k3_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_54,c_3025])).

tff(c_3659,plain,(
    ! [A_391] :
      ( r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),A_391)
      | '#skF_2'(A_391,k3_xboole_0('#skF_6','#skF_7')) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_3146,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_407,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_3'(A_111,B_112),k3_xboole_0(A_111,B_112))
      | r1_xboole_0(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_421,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_3'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | r1_xboole_0(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_179,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1100,plain,(
    ! [C_202,B_203,C_204,A_205] :
      ( ~ r2_hidden(C_202,k3_xboole_0(B_203,C_204))
      | ~ r2_hidden(C_202,A_205)
      | ~ r1_xboole_0(A_205,B_203) ) ),
    inference(resolution,[status(thm)],[c_28,c_179])).

tff(c_2442,plain,(
    ! [B_347,A_348,A_349] :
      ( ~ r2_hidden('#skF_3'(B_347,A_348),A_349)
      | ~ r1_xboole_0(A_349,A_348)
      | r1_xboole_0(B_347,A_348) ) ),
    inference(resolution,[status(thm)],[c_421,c_1100])).

tff(c_2457,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(resolution,[status(thm)],[c_421,c_2442])).

tff(c_3674,plain,
    ( r1_xboole_0('#skF_7','#skF_6')
    | '#skF_2'('#skF_6',k3_xboole_0('#skF_6','#skF_7')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3659,c_2457])).

tff(c_3702,plain,(
    '#skF_2'('#skF_6',k3_xboole_0('#skF_6','#skF_7')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1297,c_3674])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3725,plain,
    ( r2_hidden('#skF_9','#skF_6')
    | r1_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3702,c_16])).

tff(c_3870,plain,(
    r1_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3725])).

tff(c_3882,plain,(
    r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3870,c_10])).

tff(c_3889,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3882,c_2457])).

tff(c_3901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1297,c_3889])).

tff(c_3903,plain,(
    ~ r1_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3725])).

tff(c_3952,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_162,c_3903])).

tff(c_52,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1699,plain,(
    ! [A_249,B_250,B_251] :
      ( r2_hidden('#skF_1'(A_249,B_250),B_251)
      | ~ r1_tarski(A_249,B_251)
      | r1_tarski(A_249,B_250) ) ),
    inference(resolution,[status(thm)],[c_8,c_251])).

tff(c_4051,plain,(
    ! [A_396,A_397,B_398] :
      ( A_396 = '#skF_1'(A_397,B_398)
      | ~ r1_tarski(A_397,k1_tarski(A_396))
      | r1_tarski(A_397,B_398) ) ),
    inference(resolution,[status(thm)],[c_1699,c_30])).

tff(c_4115,plain,(
    ! [B_401] :
      ( '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),B_401) = '#skF_9'
      | r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_401) ) ),
    inference(resolution,[status(thm)],[c_54,c_4051])).

tff(c_190,plain,(
    ! [C_71] :
      ( ~ r2_hidden(C_71,'#skF_7')
      | ~ r2_hidden(C_71,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_203,plain,(
    ! [B_11] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_11),'#skF_8')
      | r1_xboole_0('#skF_7',B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_190])).

tff(c_999,plain,(
    ! [B_194] :
      ( ~ r1_tarski(B_194,'#skF_8')
      | r1_xboole_0('#skF_7',B_194) ) ),
    inference(resolution,[status(thm)],[c_964,c_203])).

tff(c_1015,plain,(
    ! [B_194] :
      ( r1_xboole_0(B_194,'#skF_7')
      | ~ r1_tarski(B_194,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_999,c_10])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_3'(A_15,B_16),k3_xboole_0(A_15,B_16))
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2461,plain,(
    ! [A_352,B_353] :
      ( ~ r1_xboole_0(k3_xboole_0(A_352,B_353),B_353)
      | r1_xboole_0(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_18,c_2442])).

tff(c_2575,plain,(
    ! [A_352] :
      ( r1_xboole_0(A_352,'#skF_7')
      | ~ r1_tarski(k3_xboole_0(A_352,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1015,c_2461])).

tff(c_4131,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4115,c_2575])).

tff(c_4146,plain,(
    '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_3952,c_4131])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4159,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4146,c_6])).

tff(c_4168,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4159])).

tff(c_4172,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_4168,c_2575])).

tff(c_4178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3952,c_4172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.13/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.23  
% 6.13/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 6.13/2.23  
% 6.13/2.23  %Foreground sorts:
% 6.13/2.23  
% 6.13/2.23  
% 6.13/2.23  %Background operators:
% 6.13/2.23  
% 6.13/2.23  
% 6.13/2.23  %Foreground operators:
% 6.13/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.13/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.13/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.13/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.13/2.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.13/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.13/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.13/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.13/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.13/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.13/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.13/2.23  tff('#skF_9', type, '#skF_9': $i).
% 6.13/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.13/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.13/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.13/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.13/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.13/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.13/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.13/2.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.13/2.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.13/2.23  
% 6.13/2.24  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.13/2.24  tff(f_70, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.13/2.24  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.13/2.24  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.13/2.24  tff(f_86, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.13/2.24  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.13/2.24  tff(f_99, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.13/2.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.13/2.24  tff(f_92, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 6.13/2.24  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.13/2.24  tff(c_141, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.13/2.24  tff(c_162, plain, (![A_59, B_60, A_10]: (~r1_xboole_0(A_59, B_60) | r1_xboole_0(A_10, k3_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_14, c_141])).
% 6.13/2.24  tff(c_50, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.24  tff(c_104, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | ~r1_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.13/2.24  tff(c_107, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_104])).
% 6.13/2.24  tff(c_479, plain, (![A_121, C_122, B_123]: (~r1_xboole_0(A_121, C_122) | ~r1_xboole_0(A_121, B_123) | r1_xboole_0(A_121, k2_xboole_0(B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.13/2.24  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.13/2.24  tff(c_1263, plain, (![B_223, C_224, A_225]: (r1_xboole_0(k2_xboole_0(B_223, C_224), A_225) | ~r1_xboole_0(A_225, C_224) | ~r1_xboole_0(A_225, B_223))), inference(resolution, [status(thm)], [c_479, c_10])).
% 6.13/2.24  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_6', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.24  tff(c_1286, plain, (~r1_xboole_0('#skF_7', '#skF_8') | ~r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1263, c_48])).
% 6.13/2.24  tff(c_1297, plain, (~r1_xboole_0('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1286])).
% 6.13/2.24  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.24  tff(c_251, plain, (![C_78, B_79, A_80]: (r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.13/2.24  tff(c_964, plain, (![A_191, B_192, B_193]: (r2_hidden('#skF_2'(A_191, B_192), B_193) | ~r1_tarski(B_192, B_193) | r1_xboole_0(A_191, B_192))), inference(resolution, [status(thm)], [c_14, c_251])).
% 6.13/2.24  tff(c_30, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.13/2.24  tff(c_3025, plain, (![A_368, A_369, B_370]: (A_368='#skF_2'(A_369, B_370) | ~r1_tarski(B_370, k1_tarski(A_368)) | r1_xboole_0(A_369, B_370))), inference(resolution, [status(thm)], [c_964, c_30])).
% 6.13/2.24  tff(c_3146, plain, (![A_374]: ('#skF_2'(A_374, k3_xboole_0('#skF_6', '#skF_7'))='#skF_9' | r1_xboole_0(A_374, k3_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_54, c_3025])).
% 6.13/2.24  tff(c_3659, plain, (![A_391]: (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), A_391) | '#skF_2'(A_391, k3_xboole_0('#skF_6', '#skF_7'))='#skF_9')), inference(resolution, [status(thm)], [c_3146, c_10])).
% 6.13/2.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.13/2.24  tff(c_407, plain, (![A_111, B_112]: (r2_hidden('#skF_3'(A_111, B_112), k3_xboole_0(A_111, B_112)) | r1_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.13/2.24  tff(c_421, plain, (![B_2, A_1]: (r2_hidden('#skF_3'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_407])).
% 6.13/2.24  tff(c_28, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | r1_xboole_0(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.13/2.24  tff(c_179, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.13/2.24  tff(c_1100, plain, (![C_202, B_203, C_204, A_205]: (~r2_hidden(C_202, k3_xboole_0(B_203, C_204)) | ~r2_hidden(C_202, A_205) | ~r1_xboole_0(A_205, B_203))), inference(resolution, [status(thm)], [c_28, c_179])).
% 6.13/2.24  tff(c_2442, plain, (![B_347, A_348, A_349]: (~r2_hidden('#skF_3'(B_347, A_348), A_349) | ~r1_xboole_0(A_349, A_348) | r1_xboole_0(B_347, A_348))), inference(resolution, [status(thm)], [c_421, c_1100])).
% 6.13/2.24  tff(c_2457, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(resolution, [status(thm)], [c_421, c_2442])).
% 6.13/2.24  tff(c_3674, plain, (r1_xboole_0('#skF_7', '#skF_6') | '#skF_2'('#skF_6', k3_xboole_0('#skF_6', '#skF_7'))='#skF_9'), inference(resolution, [status(thm)], [c_3659, c_2457])).
% 6.13/2.24  tff(c_3702, plain, ('#skF_2'('#skF_6', k3_xboole_0('#skF_6', '#skF_7'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_1297, c_3674])).
% 6.13/2.24  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.13/2.24  tff(c_3725, plain, (r2_hidden('#skF_9', '#skF_6') | r1_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3702, c_16])).
% 6.13/2.24  tff(c_3870, plain, (r1_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_3725])).
% 6.13/2.24  tff(c_3882, plain, (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_3870, c_10])).
% 6.13/2.24  tff(c_3889, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3882, c_2457])).
% 6.13/2.24  tff(c_3901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1297, c_3889])).
% 6.13/2.24  tff(c_3903, plain, (~r1_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_3725])).
% 6.13/2.24  tff(c_3952, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_162, c_3903])).
% 6.13/2.24  tff(c_52, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.13/2.24  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.13/2.24  tff(c_1699, plain, (![A_249, B_250, B_251]: (r2_hidden('#skF_1'(A_249, B_250), B_251) | ~r1_tarski(A_249, B_251) | r1_tarski(A_249, B_250))), inference(resolution, [status(thm)], [c_8, c_251])).
% 6.13/2.24  tff(c_4051, plain, (![A_396, A_397, B_398]: (A_396='#skF_1'(A_397, B_398) | ~r1_tarski(A_397, k1_tarski(A_396)) | r1_tarski(A_397, B_398))), inference(resolution, [status(thm)], [c_1699, c_30])).
% 6.13/2.24  tff(c_4115, plain, (![B_401]: ('#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), B_401)='#skF_9' | r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_401))), inference(resolution, [status(thm)], [c_54, c_4051])).
% 6.13/2.24  tff(c_190, plain, (![C_71]: (~r2_hidden(C_71, '#skF_7') | ~r2_hidden(C_71, '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_179])).
% 6.13/2.24  tff(c_203, plain, (![B_11]: (~r2_hidden('#skF_2'('#skF_7', B_11), '#skF_8') | r1_xboole_0('#skF_7', B_11))), inference(resolution, [status(thm)], [c_16, c_190])).
% 6.13/2.24  tff(c_999, plain, (![B_194]: (~r1_tarski(B_194, '#skF_8') | r1_xboole_0('#skF_7', B_194))), inference(resolution, [status(thm)], [c_964, c_203])).
% 6.13/2.24  tff(c_1015, plain, (![B_194]: (r1_xboole_0(B_194, '#skF_7') | ~r1_tarski(B_194, '#skF_8'))), inference(resolution, [status(thm)], [c_999, c_10])).
% 6.13/2.24  tff(c_18, plain, (![A_15, B_16]: (r2_hidden('#skF_3'(A_15, B_16), k3_xboole_0(A_15, B_16)) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.13/2.24  tff(c_2461, plain, (![A_352, B_353]: (~r1_xboole_0(k3_xboole_0(A_352, B_353), B_353) | r1_xboole_0(A_352, B_353))), inference(resolution, [status(thm)], [c_18, c_2442])).
% 6.13/2.24  tff(c_2575, plain, (![A_352]: (r1_xboole_0(A_352, '#skF_7') | ~r1_tarski(k3_xboole_0(A_352, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_1015, c_2461])).
% 6.13/2.24  tff(c_4131, plain, (r1_xboole_0('#skF_6', '#skF_7') | '#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_4115, c_2575])).
% 6.13/2.24  tff(c_4146, plain, ('#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_3952, c_4131])).
% 6.13/2.24  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.13/2.24  tff(c_4159, plain, (~r2_hidden('#skF_9', '#skF_8') | r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4146, c_6])).
% 6.13/2.24  tff(c_4168, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4159])).
% 6.13/2.24  tff(c_4172, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_4168, c_2575])).
% 6.13/2.24  tff(c_4178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3952, c_4172])).
% 6.13/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.13/2.24  
% 6.13/2.24  Inference rules
% 6.13/2.24  ----------------------
% 6.13/2.24  #Ref     : 0
% 6.13/2.24  #Sup     : 1013
% 6.13/2.24  #Fact    : 0
% 6.13/2.24  #Define  : 0
% 6.13/2.24  #Split   : 4
% 6.13/2.24  #Chain   : 0
% 6.13/2.24  #Close   : 0
% 6.13/2.24  
% 6.13/2.24  Ordering : KBO
% 6.13/2.24  
% 6.13/2.24  Simplification rules
% 6.13/2.24  ----------------------
% 6.13/2.24  #Subsume      : 362
% 6.13/2.24  #Demod        : 41
% 6.13/2.24  #Tautology    : 73
% 6.13/2.24  #SimpNegUnit  : 10
% 6.13/2.24  #BackRed      : 0
% 6.13/2.24  
% 6.13/2.24  #Partial instantiations: 0
% 6.13/2.24  #Strategies tried      : 1
% 6.13/2.24  
% 6.13/2.24  Timing (in seconds)
% 6.13/2.24  ----------------------
% 6.13/2.25  Preprocessing        : 0.33
% 6.13/2.25  Parsing              : 0.18
% 6.13/2.25  CNF conversion       : 0.02
% 6.13/2.25  Main loop            : 1.09
% 6.13/2.25  Inferencing          : 0.34
% 6.13/2.25  Reduction            : 0.32
% 6.13/2.25  Demodulation         : 0.23
% 6.13/2.25  BG Simplification    : 0.04
% 6.13/2.25  Subsumption          : 0.32
% 6.13/2.25  Abstraction          : 0.04
% 6.13/2.25  MUC search           : 0.00
% 6.13/2.25  Cooper               : 0.00
% 6.13/2.25  Total                : 1.46
% 6.13/2.25  Index Insertion      : 0.00
% 6.13/2.25  Index Deletion       : 0.00
% 6.13/2.25  Index Matching       : 0.00
% 6.13/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
