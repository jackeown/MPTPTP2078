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
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 253 expanded)
%              Number of leaves         :   21 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 628 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_72,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_81,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_724,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | ~ r1_ordinal1(A_87,B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_28,plain,(
    ! [A_17] :
      ( v3_ordinal1(k1_ordinal1(A_17))
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_265,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | B_56 = A_57
      | r2_hidden(A_57,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_378,plain,(
    ! [B_60,A_61] :
      ( ~ r1_tarski(B_60,A_61)
      | r2_hidden(B_60,A_61)
      | B_60 = A_61
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_61) ) ),
    inference(resolution,[status(thm)],[c_265,c_30])).

tff(c_417,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_378,c_63])).

tff(c_432,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_417])).

tff(c_434,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_437,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_434])).

tff(c_440,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_437])).

tff(c_26,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,A_14)
      | r1_ordinal1(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_150,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ r1_ordinal1(A_47,B_48)
      | ~ v3_ordinal1(B_48)
      | ~ v3_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_368,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_ordinal1(A_59,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_59) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_443,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_ordinal1(B_62,A_63)
      | ~ r1_ordinal1(A_63,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v3_ordinal1(A_63) ) ),
    inference(resolution,[status(thm)],[c_14,c_368])).

tff(c_457,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_443])).

tff(c_469,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_457])).

tff(c_470,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_473,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_470])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_473])).

tff(c_479,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_65,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | r2_hidden(A_28,k1_ordinal1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(k1_ordinal1(B_29),A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_65,c_30])).

tff(c_493,plain,(
    ! [B_66,B_67] :
      ( ~ r2_hidden(B_66,B_67)
      | ~ r1_ordinal1(k1_ordinal1(B_67),B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(k1_ordinal1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_150,c_69])).

tff(c_519,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_493])).

tff(c_528,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_32,c_519])).

tff(c_540,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_528])).

tff(c_554,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_540])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_554])).

tff(c_557,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_560,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_64])).

tff(c_20,plain,(
    ! [B_10] : r2_hidden(B_10,k1_ordinal1(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [B_24,A_25] :
      ( ~ r1_tarski(B_24,A_25)
      | ~ r2_hidden(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [B_10] : ~ r1_tarski(k1_ordinal1(B_10),B_10) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_167,plain,(
    ! [B_48] :
      ( ~ r1_ordinal1(k1_ordinal1(B_48),B_48)
      | ~ v3_ordinal1(B_48)
      | ~ v3_ordinal1(k1_ordinal1(B_48)) ) ),
    inference(resolution,[status(thm)],[c_150,c_52])).

tff(c_586,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_560,c_167])).

tff(c_589,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_586])).

tff(c_592,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_589])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_592])).

tff(c_597,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_597])).

tff(c_601,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_613,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_601,c_30])).

tff(c_736,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_724,c_613])).

tff(c_746,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_736])).

tff(c_750,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_746])).

tff(c_756,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_750])).

tff(c_693,plain,(
    ! [B_82,A_83] :
      ( r1_ordinal1(B_82,A_83)
      | r1_ordinal1(A_83,B_82)
      | ~ v3_ordinal1(B_82)
      | ~ v3_ordinal1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_600,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_602,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_602])).

tff(c_609,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_696,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_693,c_609])).

tff(c_702,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_696])).

tff(c_707,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_702])).

tff(c_710,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_707])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_710])).

tff(c_716,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_773,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | r1_ordinal1(A_92,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | r2_hidden(A_9,B_10)
      | ~ r2_hidden(A_9,k1_ordinal1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1066,plain,(
    ! [B_107,B_106] :
      ( B_107 = B_106
      | r2_hidden(B_106,B_107)
      | r1_ordinal1(k1_ordinal1(B_107),B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(k1_ordinal1(B_107)) ) ),
    inference(resolution,[status(thm)],[c_773,c_18])).

tff(c_1078,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1066,c_609])).

tff(c_1085,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_32,c_1078])).

tff(c_1086,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_1090,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1086,c_30])).

tff(c_1093,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1090])).

tff(c_1097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_756,c_1093])).

tff(c_1098,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1085])).

tff(c_1104,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_613])).

tff(c_1109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.99/1.47  
% 2.99/1.47  %Foreground sorts:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Background operators:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Foreground operators:
% 2.99/1.47  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.47  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.99/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.47  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.47  
% 2.99/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.49  tff(f_100, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.99/1.49  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.99/1.49  tff(f_49, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.99/1.49  tff(f_85, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.99/1.49  tff(f_72, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.99/1.49  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.99/1.49  tff(f_81, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.99/1.49  tff(f_57, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.99/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.49  tff(c_34, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.99/1.49  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.99/1.49  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.49  tff(c_724, plain, (![A_87, B_88]: (r1_tarski(A_87, B_88) | ~r1_ordinal1(A_87, B_88) | ~v3_ordinal1(B_88) | ~v3_ordinal1(A_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.49  tff(c_36, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.99/1.49  tff(c_63, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 2.99/1.49  tff(c_28, plain, (![A_17]: (v3_ordinal1(k1_ordinal1(A_17)) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.99/1.49  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.49  tff(c_265, plain, (![B_56, A_57]: (r2_hidden(B_56, A_57) | B_56=A_57 | r2_hidden(A_57, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.99/1.49  tff(c_30, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.49  tff(c_378, plain, (![B_60, A_61]: (~r1_tarski(B_60, A_61) | r2_hidden(B_60, A_61) | B_60=A_61 | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_61))), inference(resolution, [status(thm)], [c_265, c_30])).
% 2.99/1.49  tff(c_417, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_378, c_63])).
% 2.99/1.49  tff(c_432, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_417])).
% 2.99/1.49  tff(c_434, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_432])).
% 2.99/1.49  tff(c_437, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_434])).
% 2.99/1.49  tff(c_440, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_437])).
% 2.99/1.49  tff(c_26, plain, (![B_16, A_14]: (r2_hidden(B_16, A_14) | r1_ordinal1(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.49  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.99/1.49  tff(c_64, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.99/1.49  tff(c_150, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~r1_ordinal1(A_47, B_48) | ~v3_ordinal1(B_48) | ~v3_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.49  tff(c_368, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_ordinal1(A_59, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_59))), inference(resolution, [status(thm)], [c_150, c_2])).
% 2.99/1.49  tff(c_443, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_ordinal1(B_62, A_63) | ~r1_ordinal1(A_63, B_62) | ~v3_ordinal1(B_62) | ~v3_ordinal1(A_63))), inference(resolution, [status(thm)], [c_14, c_368])).
% 2.99/1.49  tff(c_457, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_443])).
% 2.99/1.49  tff(c_469, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_457])).
% 2.99/1.49  tff(c_470, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_469])).
% 2.99/1.49  tff(c_473, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_470])).
% 2.99/1.49  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_473])).
% 2.99/1.49  tff(c_479, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_469])).
% 2.99/1.49  tff(c_65, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | r2_hidden(A_28, k1_ordinal1(B_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.49  tff(c_69, plain, (![B_29, A_28]: (~r1_tarski(k1_ordinal1(B_29), A_28) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_65, c_30])).
% 2.99/1.49  tff(c_493, plain, (![B_66, B_67]: (~r2_hidden(B_66, B_67) | ~r1_ordinal1(k1_ordinal1(B_67), B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(k1_ordinal1(B_67)))), inference(resolution, [status(thm)], [c_150, c_69])).
% 2.99/1.49  tff(c_519, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_493])).
% 2.99/1.49  tff(c_528, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_32, c_519])).
% 2.99/1.49  tff(c_540, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_528])).
% 2.99/1.49  tff(c_554, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_540])).
% 2.99/1.49  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_554])).
% 2.99/1.49  tff(c_557, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_432])).
% 2.99/1.49  tff(c_560, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_64])).
% 2.99/1.49  tff(c_20, plain, (![B_10]: (r2_hidden(B_10, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.49  tff(c_48, plain, (![B_24, A_25]: (~r1_tarski(B_24, A_25) | ~r2_hidden(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.49  tff(c_52, plain, (![B_10]: (~r1_tarski(k1_ordinal1(B_10), B_10))), inference(resolution, [status(thm)], [c_20, c_48])).
% 2.99/1.49  tff(c_167, plain, (![B_48]: (~r1_ordinal1(k1_ordinal1(B_48), B_48) | ~v3_ordinal1(B_48) | ~v3_ordinal1(k1_ordinal1(B_48)))), inference(resolution, [status(thm)], [c_150, c_52])).
% 2.99/1.49  tff(c_586, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_560, c_167])).
% 2.99/1.49  tff(c_589, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_586])).
% 2.99/1.49  tff(c_592, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_589])).
% 2.99/1.49  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_592])).
% 2.99/1.49  tff(c_597, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.99/1.49  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_597])).
% 2.99/1.49  tff(c_601, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.99/1.49  tff(c_613, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_601, c_30])).
% 2.99/1.49  tff(c_736, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_724, c_613])).
% 2.99/1.49  tff(c_746, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_736])).
% 2.99/1.49  tff(c_750, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_746])).
% 2.99/1.49  tff(c_756, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_750])).
% 2.99/1.49  tff(c_693, plain, (![B_82, A_83]: (r1_ordinal1(B_82, A_83) | r1_ordinal1(A_83, B_82) | ~v3_ordinal1(B_82) | ~v3_ordinal1(A_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.49  tff(c_600, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.99/1.49  tff(c_602, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.99/1.49  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_600, c_602])).
% 2.99/1.49  tff(c_609, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.99/1.49  tff(c_696, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_693, c_609])).
% 2.99/1.49  tff(c_702, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_696])).
% 2.99/1.49  tff(c_707, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_702])).
% 2.99/1.49  tff(c_710, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_707])).
% 2.99/1.49  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_710])).
% 2.99/1.49  tff(c_716, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_702])).
% 2.99/1.49  tff(c_773, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | r1_ordinal1(A_92, B_91) | ~v3_ordinal1(B_91) | ~v3_ordinal1(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.49  tff(c_18, plain, (![B_10, A_9]: (B_10=A_9 | r2_hidden(A_9, B_10) | ~r2_hidden(A_9, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.49  tff(c_1066, plain, (![B_107, B_106]: (B_107=B_106 | r2_hidden(B_106, B_107) | r1_ordinal1(k1_ordinal1(B_107), B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(k1_ordinal1(B_107)))), inference(resolution, [status(thm)], [c_773, c_18])).
% 2.99/1.49  tff(c_1078, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_1066, c_609])).
% 2.99/1.49  tff(c_1085, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_32, c_1078])).
% 2.99/1.49  tff(c_1086, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1085])).
% 2.99/1.49  tff(c_1090, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1086, c_30])).
% 2.99/1.49  tff(c_1093, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1090])).
% 2.99/1.49  tff(c_1097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_756, c_1093])).
% 2.99/1.49  tff(c_1098, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1085])).
% 2.99/1.49  tff(c_1104, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_613])).
% 2.99/1.49  tff(c_1109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1104])).
% 2.99/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  Inference rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Ref     : 0
% 2.99/1.49  #Sup     : 183
% 2.99/1.49  #Fact    : 8
% 2.99/1.49  #Define  : 0
% 2.99/1.49  #Split   : 8
% 2.99/1.49  #Chain   : 0
% 2.99/1.49  #Close   : 0
% 2.99/1.49  
% 2.99/1.49  Ordering : KBO
% 2.99/1.49  
% 2.99/1.49  Simplification rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Subsume      : 29
% 2.99/1.49  #Demod        : 71
% 2.99/1.49  #Tautology    : 43
% 2.99/1.49  #SimpNegUnit  : 5
% 2.99/1.49  #BackRed      : 11
% 2.99/1.49  
% 2.99/1.49  #Partial instantiations: 0
% 2.99/1.49  #Strategies tried      : 1
% 2.99/1.49  
% 2.99/1.49  Timing (in seconds)
% 2.99/1.49  ----------------------
% 2.99/1.49  Preprocessing        : 0.31
% 2.99/1.49  Parsing              : 0.17
% 2.99/1.49  CNF conversion       : 0.02
% 2.99/1.49  Main loop            : 0.41
% 2.99/1.49  Inferencing          : 0.15
% 2.99/1.49  Reduction            : 0.10
% 2.99/1.49  Demodulation         : 0.07
% 2.99/1.49  BG Simplification    : 0.02
% 2.99/1.49  Subsumption          : 0.09
% 2.99/1.49  Abstraction          : 0.02
% 2.99/1.49  MUC search           : 0.00
% 2.99/1.49  Cooper               : 0.00
% 2.99/1.49  Total                : 0.75
% 2.99/1.49  Index Insertion      : 0.00
% 2.99/1.49  Index Deletion       : 0.00
% 2.99/1.49  Index Matching       : 0.00
% 2.99/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
