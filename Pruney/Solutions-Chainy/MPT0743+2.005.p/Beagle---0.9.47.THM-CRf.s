%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:09 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 180 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 388 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_75,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_68,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_106,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    ! [A_43] :
      ( v3_ordinal1(k1_ordinal1(A_43))
      | ~ v3_ordinal1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_81,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_32,plain,(
    ! [A_42] : k2_xboole_0(A_42,k1_tarski(A_42)) = k1_ordinal1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_640,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(A_121,B_122)
      | ~ r1_ordinal1(A_121,B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2185,plain,(
    ! [A_229,B_230,B_231] :
      ( r1_tarski(A_229,B_230)
      | ~ r1_ordinal1(k2_xboole_0(A_229,B_231),B_230)
      | ~ v3_ordinal1(B_230)
      | ~ v3_ordinal1(k2_xboole_0(A_229,B_231)) ) ),
    inference(resolution,[status(thm)],[c_640,c_10])).

tff(c_2207,plain,(
    ! [A_42,B_230] :
      ( r1_tarski(A_42,B_230)
      | ~ r1_ordinal1(k1_ordinal1(A_42),B_230)
      | ~ v3_ordinal1(B_230)
      | ~ v3_ordinal1(k2_xboole_0(A_42,k1_tarski(A_42))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2185])).

tff(c_3045,plain,(
    ! [A_284,B_285] :
      ( r1_tarski(A_284,B_285)
      | ~ r1_ordinal1(k1_ordinal1(A_284),B_285)
      | ~ v3_ordinal1(B_285)
      | ~ v3_ordinal1(k1_ordinal1(A_284)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2207])).

tff(c_3079,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_81,c_3045])).

tff(c_3094,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3079])).

tff(c_3095,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3094])).

tff(c_3098,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3095])).

tff(c_3102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3098])).

tff(c_3104,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3094])).

tff(c_798,plain,(
    ! [B_134,A_135] :
      ( r2_hidden(B_134,A_135)
      | r1_ordinal1(A_135,B_134)
      | ~ v3_ordinal1(B_134)
      | ~ v3_ordinal1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_58])).

tff(c_837,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_798,c_126])).

tff(c_862,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_837])).

tff(c_3103,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3094])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_665,plain,(
    ! [B_122,A_121] :
      ( B_122 = A_121
      | ~ r1_tarski(B_122,A_121)
      | ~ r1_ordinal1(A_121,B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(A_121) ) ),
    inference(resolution,[status(thm)],[c_640,c_4])).

tff(c_3107,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3103,c_665])).

tff(c_3115,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_862,c_3107])).

tff(c_3123,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3115,c_81])).

tff(c_44,plain,(
    ! [B_47] : r2_hidden(B_47,k1_ordinal1(B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(B_66,A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    ! [B_47] : ~ r1_tarski(k1_ordinal1(B_47),B_47) ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_667,plain,(
    ! [B_122] :
      ( ~ r1_ordinal1(k1_ordinal1(B_122),B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(k1_ordinal1(B_122)) ) ),
    inference(resolution,[status(thm)],[c_640,c_91])).

tff(c_3144,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3123,c_667])).

tff(c_3151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_56,c_3144])).

tff(c_3152,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3179,plain,(
    ! [B_291,A_292] :
      ( ~ r2_hidden(B_291,A_292)
      | ~ r2_hidden(A_292,B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3184,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3152,c_3179])).

tff(c_3951,plain,(
    ! [B_357,A_358] :
      ( r1_ordinal1(B_357,A_358)
      | r1_ordinal1(A_358,B_357)
      | ~ v3_ordinal1(B_357)
      | ~ v3_ordinal1(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3153,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3957,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3951,c_3153])).

tff(c_3969,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3957])).

tff(c_3976,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3969])).

tff(c_3979,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3976])).

tff(c_3983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3979])).

tff(c_3985,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3969])).

tff(c_3839,plain,(
    ! [B_353,A_354] :
      ( r2_hidden(B_353,A_354)
      | r1_ordinal1(A_354,B_353)
      | ~ v3_ordinal1(B_353)
      | ~ v3_ordinal1(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [B_47,A_46] :
      ( B_47 = A_46
      | r2_hidden(A_46,B_47)
      | ~ r2_hidden(A_46,k1_ordinal1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5339,plain,(
    ! [B_454,B_453] :
      ( B_454 = B_453
      | r2_hidden(B_454,B_453)
      | r1_ordinal1(k1_ordinal1(B_453),B_454)
      | ~ v3_ordinal1(B_454)
      | ~ v3_ordinal1(k1_ordinal1(B_453)) ) ),
    inference(resolution,[status(thm)],[c_3839,c_42])).

tff(c_5342,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5339,c_3153])).

tff(c_5345,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_54,c_5342])).

tff(c_5346,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_3184,c_5345])).

tff(c_3169,plain,(
    ! [B_288,A_289] :
      ( ~ r1_tarski(B_288,A_289)
      | ~ r2_hidden(A_289,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3176,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3152,c_3169])).

tff(c_5351,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5346,c_3176])).

tff(c_5357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.16  
% 5.89/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.17  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 5.89/2.17  
% 5.89/2.17  %Foreground sorts:
% 5.89/2.17  
% 5.89/2.17  
% 5.89/2.17  %Background operators:
% 5.89/2.17  
% 5.89/2.17  
% 5.89/2.17  %Foreground operators:
% 5.89/2.17  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.89/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.89/2.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.89/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.89/2.17  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.89/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.89/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.89/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.17  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.89/2.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.89/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.89/2.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.89/2.17  
% 5.89/2.18  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.89/2.18  tff(f_116, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.89/2.18  tff(f_75, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 5.89/2.18  tff(f_68, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.89/2.18  tff(f_83, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.89/2.18  tff(f_40, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.89/2.18  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.89/2.18  tff(f_89, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.89/2.18  tff(f_106, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.89/2.18  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.89/2.18  tff(f_66, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.89/2.18  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/2.18  tff(c_56, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.89/2.18  tff(c_34, plain, (![A_43]: (v3_ordinal1(k1_ordinal1(A_43)) | ~v3_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.89/2.18  tff(c_54, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.89/2.18  tff(c_64, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.89/2.18  tff(c_81, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 5.89/2.18  tff(c_32, plain, (![A_42]: (k2_xboole_0(A_42, k1_tarski(A_42))=k1_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.18  tff(c_640, plain, (![A_121, B_122]: (r1_tarski(A_121, B_122) | ~r1_ordinal1(A_121, B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(A_121))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.89/2.18  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.89/2.18  tff(c_2185, plain, (![A_229, B_230, B_231]: (r1_tarski(A_229, B_230) | ~r1_ordinal1(k2_xboole_0(A_229, B_231), B_230) | ~v3_ordinal1(B_230) | ~v3_ordinal1(k2_xboole_0(A_229, B_231)))), inference(resolution, [status(thm)], [c_640, c_10])).
% 5.89/2.18  tff(c_2207, plain, (![A_42, B_230]: (r1_tarski(A_42, B_230) | ~r1_ordinal1(k1_ordinal1(A_42), B_230) | ~v3_ordinal1(B_230) | ~v3_ordinal1(k2_xboole_0(A_42, k1_tarski(A_42))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2185])).
% 5.89/2.18  tff(c_3045, plain, (![A_284, B_285]: (r1_tarski(A_284, B_285) | ~r1_ordinal1(k1_ordinal1(A_284), B_285) | ~v3_ordinal1(B_285) | ~v3_ordinal1(k1_ordinal1(A_284)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2207])).
% 5.89/2.18  tff(c_3079, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_81, c_3045])).
% 5.89/2.18  tff(c_3094, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3079])).
% 5.89/2.18  tff(c_3095, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_3094])).
% 5.89/2.18  tff(c_3098, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3095])).
% 5.89/2.18  tff(c_3102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3098])).
% 5.89/2.18  tff(c_3104, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_3094])).
% 5.89/2.18  tff(c_798, plain, (![B_134, A_135]: (r2_hidden(B_134, A_135) | r1_ordinal1(A_135, B_134) | ~v3_ordinal1(B_134) | ~v3_ordinal1(A_135))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.18  tff(c_58, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.89/2.18  tff(c_126, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_58])).
% 5.89/2.18  tff(c_837, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_798, c_126])).
% 5.89/2.18  tff(c_862, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_837])).
% 5.89/2.18  tff(c_3103, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_3094])).
% 5.89/2.18  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/2.18  tff(c_665, plain, (![B_122, A_121]: (B_122=A_121 | ~r1_tarski(B_122, A_121) | ~r1_ordinal1(A_121, B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(A_121))), inference(resolution, [status(thm)], [c_640, c_4])).
% 5.89/2.18  tff(c_3107, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_3103, c_665])).
% 5.89/2.18  tff(c_3115, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_862, c_3107])).
% 5.89/2.18  tff(c_3123, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3115, c_81])).
% 5.89/2.18  tff(c_44, plain, (![B_47]: (r2_hidden(B_47, k1_ordinal1(B_47)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.89/2.18  tff(c_87, plain, (![B_66, A_67]: (~r1_tarski(B_66, A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.89/2.18  tff(c_91, plain, (![B_47]: (~r1_tarski(k1_ordinal1(B_47), B_47))), inference(resolution, [status(thm)], [c_44, c_87])).
% 5.89/2.18  tff(c_667, plain, (![B_122]: (~r1_ordinal1(k1_ordinal1(B_122), B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(k1_ordinal1(B_122)))), inference(resolution, [status(thm)], [c_640, c_91])).
% 5.89/2.18  tff(c_3144, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_3123, c_667])).
% 5.89/2.18  tff(c_3151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3104, c_56, c_3144])).
% 5.89/2.18  tff(c_3152, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 5.89/2.18  tff(c_3179, plain, (![B_291, A_292]: (~r2_hidden(B_291, A_292) | ~r2_hidden(A_292, B_291))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.89/2.18  tff(c_3184, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3152, c_3179])).
% 5.89/2.18  tff(c_3951, plain, (![B_357, A_358]: (r1_ordinal1(B_357, A_358) | r1_ordinal1(A_358, B_357) | ~v3_ordinal1(B_357) | ~v3_ordinal1(A_358))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.89/2.18  tff(c_3153, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 5.89/2.18  tff(c_3957, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_3951, c_3153])).
% 5.89/2.18  tff(c_3969, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3957])).
% 5.89/2.18  tff(c_3976, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_3969])).
% 5.89/2.18  tff(c_3979, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3976])).
% 5.89/2.18  tff(c_3983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3979])).
% 5.89/2.18  tff(c_3985, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_3969])).
% 5.89/2.18  tff(c_3839, plain, (![B_353, A_354]: (r2_hidden(B_353, A_354) | r1_ordinal1(A_354, B_353) | ~v3_ordinal1(B_353) | ~v3_ordinal1(A_354))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.18  tff(c_42, plain, (![B_47, A_46]: (B_47=A_46 | r2_hidden(A_46, B_47) | ~r2_hidden(A_46, k1_ordinal1(B_47)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.89/2.18  tff(c_5339, plain, (![B_454, B_453]: (B_454=B_453 | r2_hidden(B_454, B_453) | r1_ordinal1(k1_ordinal1(B_453), B_454) | ~v3_ordinal1(B_454) | ~v3_ordinal1(k1_ordinal1(B_453)))), inference(resolution, [status(thm)], [c_3839, c_42])).
% 5.89/2.18  tff(c_5342, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_5339, c_3153])).
% 5.89/2.18  tff(c_5345, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_54, c_5342])).
% 5.89/2.18  tff(c_5346, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_3184, c_5345])).
% 5.89/2.18  tff(c_3169, plain, (![B_288, A_289]: (~r1_tarski(B_288, A_289) | ~r2_hidden(A_289, B_288))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.89/2.18  tff(c_3176, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3152, c_3169])).
% 5.89/2.18  tff(c_5351, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5346, c_3176])).
% 5.89/2.18  tff(c_5357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5351])).
% 5.89/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.18  
% 5.89/2.18  Inference rules
% 5.89/2.18  ----------------------
% 5.89/2.18  #Ref     : 0
% 5.89/2.18  #Sup     : 1122
% 5.89/2.18  #Fact    : 4
% 5.89/2.18  #Define  : 0
% 5.89/2.18  #Split   : 3
% 5.89/2.18  #Chain   : 0
% 5.89/2.18  #Close   : 0
% 5.89/2.18  
% 5.89/2.18  Ordering : KBO
% 5.89/2.18  
% 5.89/2.18  Simplification rules
% 5.89/2.18  ----------------------
% 5.89/2.18  #Subsume      : 93
% 5.89/2.18  #Demod        : 226
% 5.89/2.18  #Tautology    : 226
% 5.89/2.18  #SimpNegUnit  : 7
% 5.89/2.18  #BackRed      : 13
% 5.89/2.18  
% 5.89/2.18  #Partial instantiations: 0
% 5.89/2.18  #Strategies tried      : 1
% 5.89/2.18  
% 5.89/2.18  Timing (in seconds)
% 5.89/2.18  ----------------------
% 5.89/2.19  Preprocessing        : 0.32
% 5.89/2.19  Parsing              : 0.17
% 5.89/2.19  CNF conversion       : 0.02
% 5.89/2.19  Main loop            : 1.05
% 5.89/2.19  Inferencing          : 0.34
% 5.89/2.19  Reduction            : 0.37
% 5.89/2.19  Demodulation         : 0.26
% 5.89/2.19  BG Simplification    : 0.04
% 5.89/2.19  Subsumption          : 0.22
% 5.89/2.19  Abstraction          : 0.05
% 5.89/2.19  MUC search           : 0.00
% 5.89/2.19  Cooper               : 0.00
% 5.89/2.19  Total                : 1.40
% 5.89/2.19  Index Insertion      : 0.00
% 5.89/2.19  Index Deletion       : 0.00
% 5.89/2.19  Index Matching       : 0.00
% 5.89/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
