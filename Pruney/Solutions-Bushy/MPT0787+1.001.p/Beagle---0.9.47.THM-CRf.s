%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:51 EST 2020

% Result     : Theorem 11.28s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 283 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 834 expanded)
%              Number of equality atoms :   26 (  69 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_9 > #skF_7 > #skF_5 > #skF_1 > #skF_4 > #skF_8 > #skF_3 > #skF_14 > #skF_10 > #skF_13 > #skF_2 > #skF_11 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> ! [B,C] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,B),A) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

tff(c_78,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_76,plain,(
    v2_wellord1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_87,plain,(
    ! [A_47] :
      ( v1_relat_2(A_47)
      | ~ v2_wellord1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,
    ( v1_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_76,c_87])).

tff(c_93,plain,(
    v1_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_90])).

tff(c_74,plain,(
    r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    ! [B_22,A_19] :
      ( r2_hidden(k4_tarski(B_22,B_22),A_19)
      | ~ r2_hidden(B_22,k3_relat_1(A_19))
      | ~ v1_relat_2(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14')
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_102,plain,(
    r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_30,plain,(
    ! [A_18] :
      ( v6_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_971,plain,(
    ! [C_204,B_205,A_206] :
      ( r2_hidden(k4_tarski(C_204,B_205),A_206)
      | r2_hidden(k4_tarski(B_205,C_204),A_206)
      | C_204 = B_205
      | ~ r2_hidden(C_204,k3_relat_1(A_206))
      | ~ r2_hidden(B_205,k3_relat_1(A_206))
      | ~ v6_relat_2(A_206)
      | ~ v1_relat_1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ r2_hidden(k4_tarski(D_12,B_8),A_1)
      | D_12 = B_8
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4852,plain,(
    ! [B_412,A_413,C_414] :
      ( r2_hidden(B_412,k1_wellord1(A_413,C_414))
      | r2_hidden(k4_tarski(C_414,B_412),A_413)
      | C_414 = B_412
      | ~ r2_hidden(C_414,k3_relat_1(A_413))
      | ~ r2_hidden(B_412,k3_relat_1(A_413))
      | ~ v6_relat_2(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(resolution,[status(thm)],[c_971,c_2])).

tff(c_80,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13'))
    | ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_117,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_80])).

tff(c_4918,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | '#skF_13' = '#skF_12'
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ v6_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_4852,c_117])).

tff(c_4945,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | '#skF_13' = '#skF_12'
    | ~ v6_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_74,c_4918])).

tff(c_4947,plain,(
    ~ v6_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_4945])).

tff(c_4953,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_30,c_4947])).

tff(c_4960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_4953])).

tff(c_4961,plain,
    ( '#skF_13' = '#skF_12'
    | r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_4945])).

tff(c_5011,plain,(
    r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_4961])).

tff(c_20,plain,(
    ! [C_17,B_14,A_13] :
      ( r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5030,plain,(
    ! [B_417] :
      ( r2_hidden('#skF_13',B_417)
      | ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),B_417) ) ),
    inference(resolution,[status(thm)],[c_5011,c_20])).

tff(c_5047,plain,(
    r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_102,c_5030])).

tff(c_6,plain,(
    ! [D_12,A_1] :
      ( ~ r2_hidden(D_12,k1_wellord1(A_1,D_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5058,plain,(
    ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5047,c_6])).

tff(c_5073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5058])).

tff(c_5074,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_4961])).

tff(c_5124,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_12'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5074,c_117])).

tff(c_5142,plain,
    ( ~ r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ v1_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_38,c_5124])).

tff(c_5154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_93,c_74,c_5142])).

tff(c_5155,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_5158,plain,(
    ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5155,c_80])).

tff(c_4,plain,(
    ! [D_12,B_8,A_1] :
      ( r2_hidden(k4_tarski(D_12,B_8),A_1)
      | ~ r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_18] :
      ( v4_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5163,plain,(
    ! [A_424,B_425] :
      ( r2_hidden('#skF_3'(A_424,B_425),A_424)
      | r1_tarski(A_424,B_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5168,plain,(
    ! [A_424] : r1_tarski(A_424,A_424) ),
    inference(resolution,[status(thm)],[c_5163,c_22])).

tff(c_5350,plain,(
    ! [D_472,A_473,B_474] :
      ( r2_hidden(D_472,k1_wellord1(A_473,B_474))
      | ~ r2_hidden(k4_tarski(D_472,B_474),A_473)
      | D_472 = B_474
      | ~ v1_relat_1(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5374,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_14','#skF_13'))
    | '#skF_13' = '#skF_12'
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5155,c_5350])).

tff(c_5385,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_14','#skF_13'))
    | '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5374])).

tff(c_5386,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_5385])).

tff(c_5391,plain,(
    ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5386,c_5158])).

tff(c_5396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5168,c_5391])).

tff(c_5398,plain,(
    '#skF_13' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5385])).

tff(c_5409,plain,(
    ! [C_476,B_477,A_478] :
      ( C_476 = B_477
      | ~ r2_hidden(k4_tarski(C_476,B_477),A_478)
      | ~ r2_hidden(k4_tarski(B_477,C_476),A_478)
      | ~ v4_relat_2(A_478)
      | ~ v1_relat_1(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5425,plain,
    ( '#skF_13' = '#skF_12'
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5155,c_5409])).

tff(c_5438,plain,
    ( '#skF_13' = '#skF_12'
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5425])).

tff(c_5439,plain,
    ( ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_5398,c_5438])).

tff(c_5440,plain,(
    ~ v4_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_5439])).

tff(c_5446,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_32,c_5440])).

tff(c_5453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5446])).

tff(c_5454,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_5439])).

tff(c_5463,plain,
    ( ~ r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_4,c_5454])).

tff(c_5466,plain,(
    ~ r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5463])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_18] :
      ( v8_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5556,plain,(
    ! [B_508,D_509,A_510,C_511] :
      ( r2_hidden(k4_tarski(B_508,D_509),A_510)
      | ~ r2_hidden(k4_tarski(C_511,D_509),A_510)
      | ~ r2_hidden(k4_tarski(B_508,C_511),A_510)
      | ~ v8_relat_2(A_510)
      | ~ v1_relat_1(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5580,plain,(
    ! [B_508] :
      ( r2_hidden(k4_tarski(B_508,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_508,'#skF_12'),'#skF_14')
      | ~ v8_relat_2('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_5155,c_5556])).

tff(c_5594,plain,(
    ! [B_508] :
      ( r2_hidden(k4_tarski(B_508,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_508,'#skF_12'),'#skF_14')
      | ~ v8_relat_2('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5580])).

tff(c_5595,plain,(
    ~ v8_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_5594])).

tff(c_5598,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_34,c_5595])).

tff(c_5602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5598])).

tff(c_5630,plain,(
    ! [B_514] :
      ( r2_hidden(k4_tarski(B_514,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_514,'#skF_12'),'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_5594])).

tff(c_5637,plain,(
    ! [B_514] :
      ( r2_hidden(B_514,k1_wellord1('#skF_14','#skF_13'))
      | B_514 = '#skF_13'
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(k4_tarski(B_514,'#skF_12'),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_5630,c_2])).

tff(c_5673,plain,(
    ! [B_516] :
      ( r2_hidden(B_516,k1_wellord1('#skF_14','#skF_13'))
      | B_516 = '#skF_13'
      | ~ r2_hidden(k4_tarski(B_516,'#skF_12'),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5637])).

tff(c_5681,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,k1_wellord1('#skF_14','#skF_13'))
      | D_12 = '#skF_13'
      | ~ r2_hidden(D_12,k1_wellord1('#skF_14','#skF_12'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_4,c_5673])).

tff(c_5705,plain,(
    ! [D_518] :
      ( r2_hidden(D_518,k1_wellord1('#skF_14','#skF_13'))
      | D_518 = '#skF_13'
      | ~ r2_hidden(D_518,k1_wellord1('#skF_14','#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5681])).

tff(c_13582,plain,(
    ! [A_821] :
      ( r1_tarski(A_821,k1_wellord1('#skF_14','#skF_13'))
      | '#skF_3'(A_821,k1_wellord1('#skF_14','#skF_13')) = '#skF_13'
      | ~ r2_hidden('#skF_3'(A_821,k1_wellord1('#skF_14','#skF_13')),k1_wellord1('#skF_14','#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_5705,c_22])).

tff(c_13590,plain,
    ( '#skF_3'(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) = '#skF_13'
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_24,c_13582])).

tff(c_13594,plain,(
    '#skF_3'(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_5158,c_5158,c_13590])).

tff(c_13627,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13594,c_24])).

tff(c_13650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5158,c_5466,c_13627])).

%------------------------------------------------------------------------------
