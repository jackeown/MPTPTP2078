%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:46 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 271 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 798 expanded)
%              Number of equality atoms :   26 (  69 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_9 > #skF_7 > #skF_5 > #skF_4 > #skF_8 > #skF_14 > #skF_10 > #skF_13 > #skF_2 > #skF_11 > #skF_3 > #skF_1 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_109,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> ! [B,C] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,B),A) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

tff(f_79,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_76,plain,(
    v2_wellord1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_87,plain,(
    ! [A_47] :
      ( v1_relat_2(A_47)
      | ~ v2_wellord1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,
    ( v1_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_76,c_87])).

tff(c_93,plain,(
    v1_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_90])).

tff(c_74,plain,(
    r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [B_22,A_19] :
      ( r2_hidden(k4_tarski(B_22,B_22),A_19)
      | ~ r2_hidden(B_22,k3_relat_1(A_19))
      | ~ v1_relat_2(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14')
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_102,plain,(
    r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_30,plain,(
    ! [A_18] :
      ( v6_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1128,plain,(
    ! [C_222,B_223,A_224] :
      ( r2_hidden(k4_tarski(C_222,B_223),A_224)
      | r2_hidden(k4_tarski(B_223,C_222),A_224)
      | C_222 = B_223
      | ~ r2_hidden(C_222,k3_relat_1(A_224))
      | ~ r2_hidden(B_223,k3_relat_1(A_224))
      | ~ v6_relat_2(A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [D_17,A_6,B_13] :
      ( r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ r2_hidden(k4_tarski(D_17,B_13),A_6)
      | D_17 = B_13
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5201,plain,(
    ! [C_426,A_427,B_428] :
      ( r2_hidden(C_426,k1_wellord1(A_427,B_428))
      | r2_hidden(k4_tarski(B_428,C_426),A_427)
      | C_426 = B_428
      | ~ r2_hidden(C_426,k3_relat_1(A_427))
      | ~ r2_hidden(B_428,k3_relat_1(A_427))
      | ~ v6_relat_2(A_427)
      | ~ v1_relat_1(A_427) ) ),
    inference(resolution,[status(thm)],[c_1128,c_8])).

tff(c_80,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13'))
    | ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_117,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_80])).

tff(c_5270,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | '#skF_13' = '#skF_12'
    | ~ r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ v6_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5201,c_117])).

tff(c_5298,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | '#skF_13' = '#skF_12'
    | ~ v6_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_5270])).

tff(c_5300,plain,(
    ~ v6_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_5298])).

tff(c_5306,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_30,c_5300])).

tff(c_5313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5306])).

tff(c_5314,plain,
    ( '#skF_13' = '#skF_12'
    | r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_5298])).

tff(c_5317,plain,(
    r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_5314])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5336,plain,(
    ! [B_429] :
      ( r2_hidden('#skF_13',B_429)
      | ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),B_429) ) ),
    inference(resolution,[status(thm)],[c_5317,c_2])).

tff(c_5353,plain,(
    r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_102,c_5336])).

tff(c_12,plain,(
    ! [D_17,A_6] :
      ( ~ r2_hidden(D_17,k1_wellord1(A_6,D_17))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5364,plain,(
    ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5353,c_12])).

tff(c_5379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5364])).

tff(c_5380,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5314])).

tff(c_5434,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_12'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5380,c_117])).

tff(c_5452,plain,
    ( ~ r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ v1_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_38,c_5434])).

tff(c_5464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_93,c_74,c_5452])).

tff(c_5466,plain,(
    ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_10,plain,(
    ! [D_17,B_13,A_6] :
      ( r2_hidden(k4_tarski(D_17,B_13),A_6)
      | ~ r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_18] :
      ( v4_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5472,plain,(
    ! [A_437,B_438] :
      ( r2_hidden('#skF_1'(A_437,B_438),A_437)
      | r1_tarski(A_437,B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5477,plain,(
    ! [A_437] : r1_tarski(A_437,A_437) ),
    inference(resolution,[status(thm)],[c_5472,c_4])).

tff(c_5465,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_5663,plain,(
    ! [D_490,A_491,B_492] :
      ( r2_hidden(D_490,k1_wellord1(A_491,B_492))
      | ~ r2_hidden(k4_tarski(D_490,B_492),A_491)
      | D_490 = B_492
      | ~ v1_relat_1(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5687,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_14','#skF_13'))
    | '#skF_13' = '#skF_12'
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5465,c_5663])).

tff(c_5698,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_14','#skF_13'))
    | '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5687])).

tff(c_5727,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_5698])).

tff(c_5732,plain,(
    ~ r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5727,c_5466])).

tff(c_5737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5477,c_5732])).

tff(c_5739,plain,(
    '#skF_13' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5698])).

tff(c_5699,plain,(
    ! [C_493,B_494,A_495] :
      ( C_493 = B_494
      | ~ r2_hidden(k4_tarski(C_493,B_494),A_495)
      | ~ r2_hidden(k4_tarski(B_494,C_493),A_495)
      | ~ v4_relat_2(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5715,plain,
    ( '#skF_13' = '#skF_12'
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5465,c_5699])).

tff(c_5726,plain,
    ( '#skF_13' = '#skF_12'
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5715])).

tff(c_5740,plain,
    ( ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14')
    | ~ v4_relat_2('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_5739,c_5726])).

tff(c_5741,plain,(
    ~ v4_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_5740])).

tff(c_5747,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_32,c_5741])).

tff(c_5754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5747])).

tff(c_5755,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_5740])).

tff(c_5762,plain,
    ( ~ r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_10,c_5755])).

tff(c_5765,plain,(
    ~ r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5762])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_18] :
      ( v8_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5873,plain,(
    ! [B_525,D_526,A_527,C_528] :
      ( r2_hidden(k4_tarski(B_525,D_526),A_527)
      | ~ r2_hidden(k4_tarski(C_528,D_526),A_527)
      | ~ r2_hidden(k4_tarski(B_525,C_528),A_527)
      | ~ v8_relat_2(A_527)
      | ~ v1_relat_1(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5897,plain,(
    ! [B_525] :
      ( r2_hidden(k4_tarski(B_525,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_525,'#skF_12'),'#skF_14')
      | ~ v8_relat_2('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_5465,c_5873])).

tff(c_5911,plain,(
    ! [B_525] :
      ( r2_hidden(k4_tarski(B_525,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_525,'#skF_12'),'#skF_14')
      | ~ v8_relat_2('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5897])).

tff(c_5912,plain,(
    ~ v8_relat_2('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_5911])).

tff(c_5915,plain,
    ( ~ v2_wellord1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_34,c_5912])).

tff(c_5919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5915])).

tff(c_5928,plain,(
    ! [B_529] :
      ( r2_hidden(k4_tarski(B_529,'#skF_13'),'#skF_14')
      | ~ r2_hidden(k4_tarski(B_529,'#skF_12'),'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_5911])).

tff(c_5935,plain,(
    ! [B_529] :
      ( r2_hidden(B_529,k1_wellord1('#skF_14','#skF_13'))
      | B_529 = '#skF_13'
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(k4_tarski(B_529,'#skF_12'),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_5928,c_8])).

tff(c_5982,plain,(
    ! [B_534] :
      ( r2_hidden(B_534,k1_wellord1('#skF_14','#skF_13'))
      | B_534 = '#skF_13'
      | ~ r2_hidden(k4_tarski(B_534,'#skF_12'),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5935])).

tff(c_5994,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,k1_wellord1('#skF_14','#skF_13'))
      | D_17 = '#skF_13'
      | ~ r2_hidden(D_17,k1_wellord1('#skF_14','#skF_12'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_10,c_5982])).

tff(c_6028,plain,(
    ! [D_536] :
      ( r2_hidden(D_536,k1_wellord1('#skF_14','#skF_13'))
      | D_536 = '#skF_13'
      | ~ r2_hidden(D_536,k1_wellord1('#skF_14','#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5994])).

tff(c_13241,plain,(
    ! [A_820] :
      ( r1_tarski(A_820,k1_wellord1('#skF_14','#skF_13'))
      | '#skF_1'(A_820,k1_wellord1('#skF_14','#skF_13')) = '#skF_13'
      | ~ r2_hidden('#skF_1'(A_820,k1_wellord1('#skF_14','#skF_13')),k1_wellord1('#skF_14','#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_6028,c_4])).

tff(c_13249,plain,
    ( '#skF_1'(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) = '#skF_13'
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_6,c_13241])).

tff(c_13253,plain,(
    '#skF_1'(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_5466,c_5466,c_13249])).

tff(c_13286,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_14','#skF_12'))
    | r1_tarski(k1_wellord1('#skF_14','#skF_12'),k1_wellord1('#skF_14','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13253,c_6])).

tff(c_13309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5466,c_5765,c_13286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.19/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.11  
% 11.19/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.12  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_9 > #skF_7 > #skF_5 > #skF_4 > #skF_8 > #skF_14 > #skF_10 > #skF_13 > #skF_2 > #skF_11 > #skF_3 > #skF_1 > #skF_6 > #skF_12
% 11.19/4.12  
% 11.19/4.12  %Foreground sorts:
% 11.19/4.12  
% 11.19/4.12  
% 11.19/4.12  %Background operators:
% 11.19/4.12  
% 11.19/4.12  
% 11.19/4.12  %Foreground operators:
% 11.19/4.12  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.19/4.12  tff('#skF_7', type, '#skF_7': $i > $i).
% 11.19/4.12  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.19/4.12  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.19/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.19/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.19/4.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.19/4.12  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 11.19/4.12  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 11.19/4.12  tff('#skF_8', type, '#skF_8': $i > $i).
% 11.19/4.12  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 11.19/4.12  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 11.19/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.19/4.12  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 11.19/4.12  tff('#skF_14', type, '#skF_14': $i).
% 11.19/4.12  tff('#skF_10', type, '#skF_10': $i > $i).
% 11.19/4.12  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 11.19/4.12  tff('#skF_13', type, '#skF_13': $i).
% 11.19/4.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.19/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.19/4.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.19/4.12  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 11.19/4.12  tff('#skF_11', type, '#skF_11': $i > $i).
% 11.19/4.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.19/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.19/4.12  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 11.19/4.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.19/4.12  tff('#skF_6', type, '#skF_6': $i > $i).
% 11.19/4.12  tff('#skF_12', type, '#skF_12': $i).
% 11.19/4.12  
% 11.19/4.13  tff(f_122, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 11.19/4.13  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 11.19/4.13  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 11.19/4.13  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 11.19/4.13  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 11.19/4.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.19/4.13  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> (![B, C]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, B), A)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_wellord1)).
% 11.19/4.13  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> (![B, C, D]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, D), A)) => r2_hidden(k4_tarski(B, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 11.19/4.13  tff(c_78, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_76, plain, (v2_wellord1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_87, plain, (![A_47]: (v1_relat_2(A_47) | ~v2_wellord1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.19/4.13  tff(c_90, plain, (v1_relat_2('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_76, c_87])).
% 11.19/4.13  tff(c_93, plain, (v1_relat_2('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_90])).
% 11.19/4.13  tff(c_74, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_38, plain, (![B_22, A_19]: (r2_hidden(k4_tarski(B_22, B_22), A_19) | ~r2_hidden(B_22, k3_relat_1(A_19)) | ~v1_relat_2(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.19/4.13  tff(c_86, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14') | r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_102, plain, (r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))), inference(splitLeft, [status(thm)], [c_86])).
% 11.19/4.13  tff(c_30, plain, (![A_18]: (v6_relat_2(A_18) | ~v2_wellord1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.19/4.13  tff(c_72, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_1128, plain, (![C_222, B_223, A_224]: (r2_hidden(k4_tarski(C_222, B_223), A_224) | r2_hidden(k4_tarski(B_223, C_222), A_224) | C_222=B_223 | ~r2_hidden(C_222, k3_relat_1(A_224)) | ~r2_hidden(B_223, k3_relat_1(A_224)) | ~v6_relat_2(A_224) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.19/4.13  tff(c_8, plain, (![D_17, A_6, B_13]: (r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~r2_hidden(k4_tarski(D_17, B_13), A_6) | D_17=B_13 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/4.13  tff(c_5201, plain, (![C_426, A_427, B_428]: (r2_hidden(C_426, k1_wellord1(A_427, B_428)) | r2_hidden(k4_tarski(B_428, C_426), A_427) | C_426=B_428 | ~r2_hidden(C_426, k3_relat_1(A_427)) | ~r2_hidden(B_428, k3_relat_1(A_427)) | ~v6_relat_2(A_427) | ~v1_relat_1(A_427))), inference(resolution, [status(thm)], [c_1128, c_8])).
% 11.19/4.13  tff(c_80, plain, (~r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13')) | ~r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/4.13  tff(c_117, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_80])).
% 11.19/4.13  tff(c_5270, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12')) | '#skF_13'='#skF_12' | ~r2_hidden('#skF_13', k3_relat_1('#skF_14')) | ~r2_hidden('#skF_12', k3_relat_1('#skF_14')) | ~v6_relat_2('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_5201, c_117])).
% 11.19/4.13  tff(c_5298, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12')) | '#skF_13'='#skF_12' | ~v6_relat_2('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_5270])).
% 11.19/4.13  tff(c_5300, plain, (~v6_relat_2('#skF_14')), inference(splitLeft, [status(thm)], [c_5298])).
% 11.19/4.13  tff(c_5306, plain, (~v2_wellord1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_30, c_5300])).
% 11.19/4.13  tff(c_5313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5306])).
% 11.19/4.13  tff(c_5314, plain, ('#skF_13'='#skF_12' | r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12'))), inference(splitRight, [status(thm)], [c_5298])).
% 11.19/4.13  tff(c_5317, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12'))), inference(splitLeft, [status(thm)], [c_5314])).
% 11.19/4.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.13  tff(c_5336, plain, (![B_429]: (r2_hidden('#skF_13', B_429) | ~r1_tarski(k1_wellord1('#skF_14', '#skF_12'), B_429))), inference(resolution, [status(thm)], [c_5317, c_2])).
% 11.19/4.13  tff(c_5353, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_13'))), inference(resolution, [status(thm)], [c_102, c_5336])).
% 11.19/4.13  tff(c_12, plain, (![D_17, A_6]: (~r2_hidden(D_17, k1_wellord1(A_6, D_17)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/4.13  tff(c_5364, plain, (~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_5353, c_12])).
% 11.19/4.13  tff(c_5379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_5364])).
% 11.19/4.13  tff(c_5380, plain, ('#skF_13'='#skF_12'), inference(splitRight, [status(thm)], [c_5314])).
% 11.19/4.13  tff(c_5434, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_12'), '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_5380, c_117])).
% 11.19/4.13  tff(c_5452, plain, (~r2_hidden('#skF_12', k3_relat_1('#skF_14')) | ~v1_relat_2('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_38, c_5434])).
% 11.19/4.13  tff(c_5464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_93, c_74, c_5452])).
% 11.19/4.13  tff(c_5466, plain, (~r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))), inference(splitRight, [status(thm)], [c_86])).
% 11.19/4.13  tff(c_10, plain, (![D_17, B_13, A_6]: (r2_hidden(k4_tarski(D_17, B_13), A_6) | ~r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/4.13  tff(c_32, plain, (![A_18]: (v4_relat_2(A_18) | ~v2_wellord1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.19/4.13  tff(c_5472, plain, (![A_437, B_438]: (r2_hidden('#skF_1'(A_437, B_438), A_437) | r1_tarski(A_437, B_438))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.13  tff(c_5477, plain, (![A_437]: (r1_tarski(A_437, A_437))), inference(resolution, [status(thm)], [c_5472, c_4])).
% 11.19/4.13  tff(c_5465, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(splitRight, [status(thm)], [c_86])).
% 11.19/4.13  tff(c_5663, plain, (![D_490, A_491, B_492]: (r2_hidden(D_490, k1_wellord1(A_491, B_492)) | ~r2_hidden(k4_tarski(D_490, B_492), A_491) | D_490=B_492 | ~v1_relat_1(A_491))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/4.13  tff(c_5687, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_14', '#skF_13')) | '#skF_13'='#skF_12' | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_5465, c_5663])).
% 11.19/4.13  tff(c_5698, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_14', '#skF_13')) | '#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5687])).
% 11.19/4.13  tff(c_5727, plain, ('#skF_13'='#skF_12'), inference(splitLeft, [status(thm)], [c_5698])).
% 11.19/4.13  tff(c_5732, plain, (~r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5727, c_5466])).
% 11.19/4.13  tff(c_5737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5477, c_5732])).
% 11.19/4.13  tff(c_5739, plain, ('#skF_13'!='#skF_12'), inference(splitRight, [status(thm)], [c_5698])).
% 11.19/4.13  tff(c_5699, plain, (![C_493, B_494, A_495]: (C_493=B_494 | ~r2_hidden(k4_tarski(C_493, B_494), A_495) | ~r2_hidden(k4_tarski(B_494, C_493), A_495) | ~v4_relat_2(A_495) | ~v1_relat_1(A_495))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.19/4.13  tff(c_5715, plain, ('#skF_13'='#skF_12' | ~r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_14') | ~v4_relat_2('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_5465, c_5699])).
% 11.19/4.13  tff(c_5726, plain, ('#skF_13'='#skF_12' | ~r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_14') | ~v4_relat_2('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5715])).
% 11.19/4.13  tff(c_5740, plain, (~r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_14') | ~v4_relat_2('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_5739, c_5726])).
% 11.19/4.13  tff(c_5741, plain, (~v4_relat_2('#skF_14')), inference(splitLeft, [status(thm)], [c_5740])).
% 11.19/4.13  tff(c_5747, plain, (~v2_wellord1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_32, c_5741])).
% 11.19/4.13  tff(c_5754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5747])).
% 11.19/4.13  tff(c_5755, plain, (~r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_14')), inference(splitRight, [status(thm)], [c_5740])).
% 11.19/4.13  tff(c_5762, plain, (~r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_10, c_5755])).
% 11.19/4.13  tff(c_5765, plain, (~r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5762])).
% 11.19/4.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.13  tff(c_34, plain, (![A_18]: (v8_relat_2(A_18) | ~v2_wellord1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.19/4.13  tff(c_5873, plain, (![B_525, D_526, A_527, C_528]: (r2_hidden(k4_tarski(B_525, D_526), A_527) | ~r2_hidden(k4_tarski(C_528, D_526), A_527) | ~r2_hidden(k4_tarski(B_525, C_528), A_527) | ~v8_relat_2(A_527) | ~v1_relat_1(A_527))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.19/4.13  tff(c_5897, plain, (![B_525]: (r2_hidden(k4_tarski(B_525, '#skF_13'), '#skF_14') | ~r2_hidden(k4_tarski(B_525, '#skF_12'), '#skF_14') | ~v8_relat_2('#skF_14') | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_5465, c_5873])).
% 11.19/4.13  tff(c_5911, plain, (![B_525]: (r2_hidden(k4_tarski(B_525, '#skF_13'), '#skF_14') | ~r2_hidden(k4_tarski(B_525, '#skF_12'), '#skF_14') | ~v8_relat_2('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5897])).
% 11.19/4.13  tff(c_5912, plain, (~v8_relat_2('#skF_14')), inference(splitLeft, [status(thm)], [c_5911])).
% 11.19/4.13  tff(c_5915, plain, (~v2_wellord1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_34, c_5912])).
% 11.19/4.13  tff(c_5919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5915])).
% 11.19/4.13  tff(c_5928, plain, (![B_529]: (r2_hidden(k4_tarski(B_529, '#skF_13'), '#skF_14') | ~r2_hidden(k4_tarski(B_529, '#skF_12'), '#skF_14'))), inference(splitRight, [status(thm)], [c_5911])).
% 11.19/4.13  tff(c_5935, plain, (![B_529]: (r2_hidden(B_529, k1_wellord1('#skF_14', '#skF_13')) | B_529='#skF_13' | ~v1_relat_1('#skF_14') | ~r2_hidden(k4_tarski(B_529, '#skF_12'), '#skF_14'))), inference(resolution, [status(thm)], [c_5928, c_8])).
% 11.19/4.13  tff(c_5982, plain, (![B_534]: (r2_hidden(B_534, k1_wellord1('#skF_14', '#skF_13')) | B_534='#skF_13' | ~r2_hidden(k4_tarski(B_534, '#skF_12'), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5935])).
% 11.19/4.13  tff(c_5994, plain, (![D_17]: (r2_hidden(D_17, k1_wellord1('#skF_14', '#skF_13')) | D_17='#skF_13' | ~r2_hidden(D_17, k1_wellord1('#skF_14', '#skF_12')) | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_10, c_5982])).
% 11.19/4.13  tff(c_6028, plain, (![D_536]: (r2_hidden(D_536, k1_wellord1('#skF_14', '#skF_13')) | D_536='#skF_13' | ~r2_hidden(D_536, k1_wellord1('#skF_14', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5994])).
% 11.19/4.13  tff(c_13241, plain, (![A_820]: (r1_tarski(A_820, k1_wellord1('#skF_14', '#skF_13')) | '#skF_1'(A_820, k1_wellord1('#skF_14', '#skF_13'))='#skF_13' | ~r2_hidden('#skF_1'(A_820, k1_wellord1('#skF_14', '#skF_13')), k1_wellord1('#skF_14', '#skF_12')))), inference(resolution, [status(thm)], [c_6028, c_4])).
% 11.19/4.13  tff(c_13249, plain, ('#skF_1'(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))='#skF_13' | r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))), inference(resolution, [status(thm)], [c_6, c_13241])).
% 11.19/4.13  tff(c_13253, plain, ('#skF_1'(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_5466, c_5466, c_13249])).
% 11.19/4.13  tff(c_13286, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_14', '#skF_12')) | r1_tarski(k1_wellord1('#skF_14', '#skF_12'), k1_wellord1('#skF_14', '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_13253, c_6])).
% 11.19/4.13  tff(c_13309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5466, c_5765, c_13286])).
% 11.19/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.13  
% 11.19/4.13  Inference rules
% 11.19/4.13  ----------------------
% 11.19/4.13  #Ref     : 0
% 11.19/4.13  #Sup     : 2833
% 11.19/4.13  #Fact    : 4
% 11.19/4.13  #Define  : 0
% 11.19/4.13  #Split   : 25
% 11.19/4.13  #Chain   : 0
% 11.19/4.13  #Close   : 0
% 11.19/4.13  
% 11.19/4.13  Ordering : KBO
% 11.19/4.13  
% 11.19/4.13  Simplification rules
% 11.19/4.13  ----------------------
% 11.19/4.13  #Subsume      : 634
% 11.19/4.13  #Demod        : 1079
% 11.19/4.13  #Tautology    : 262
% 11.19/4.13  #SimpNegUnit  : 75
% 11.19/4.13  #BackRed      : 100
% 11.19/4.13  
% 11.19/4.13  #Partial instantiations: 0
% 11.19/4.13  #Strategies tried      : 1
% 11.19/4.13  
% 11.19/4.13  Timing (in seconds)
% 11.19/4.13  ----------------------
% 11.19/4.14  Preprocessing        : 0.38
% 11.19/4.14  Parsing              : 0.18
% 11.19/4.14  CNF conversion       : 0.03
% 11.19/4.14  Main loop            : 2.95
% 11.19/4.14  Inferencing          : 0.78
% 11.19/4.14  Reduction            : 0.68
% 11.19/4.14  Demodulation         : 0.44
% 11.19/4.14  BG Simplification    : 0.10
% 11.19/4.14  Subsumption          : 1.18
% 11.19/4.14  Abstraction          : 0.13
% 11.19/4.14  MUC search           : 0.00
% 11.19/4.14  Cooper               : 0.00
% 11.19/4.14  Total                : 3.37
% 11.19/4.14  Index Insertion      : 0.00
% 11.19/4.14  Index Deletion       : 0.00
% 11.19/4.14  Index Matching       : 0.00
% 11.19/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
