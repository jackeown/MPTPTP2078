%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 11.29s
% Output     : CNFRefutation 11.29s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 339 expanded)
%              Number of equality atoms :   21 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_69,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_68,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4538,plain,(
    ! [B_398,A_399] :
      ( r2_hidden(B_398,A_399)
      | r1_ordinal1(A_399,B_398)
      | ~ v3_ordinal1(B_398)
      | ~ v3_ordinal1(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4190,plain,(
    ! [A_357,B_358] :
      ( r1_tarski(k1_tarski(A_357),B_358)
      | ~ r2_hidden(A_357,B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4122,plain,(
    ! [D_335,A_336] : r2_hidden(D_335,k2_tarski(A_336,D_335)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4125,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4122])).

tff(c_4132,plain,(
    ! [B_340,A_341] :
      ( ~ r1_tarski(B_340,A_341)
      | ~ r2_hidden(A_341,B_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4146,plain,(
    ! [A_17] : ~ r1_tarski(k1_tarski(A_17),A_17) ),
    inference(resolution,[status(thm)],[c_4125,c_4132])).

tff(c_4195,plain,(
    ! [B_358] : ~ r2_hidden(B_358,B_358) ),
    inference(resolution,[status(thm)],[c_4190,c_4146])).

tff(c_4640,plain,(
    ! [A_399] :
      ( r1_ordinal1(A_399,A_399)
      | ~ v3_ordinal1(A_399) ) ),
    inference(resolution,[status(thm)],[c_4538,c_4195])).

tff(c_108,plain,(
    ! [D_37,A_38] : r2_hidden(D_37,k2_tarski(A_38,D_37)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_56,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_tarski(A_21)) = k1_ordinal1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | r2_hidden(D_64,k2_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1565,plain,(
    ! [D_207,A_208] :
      ( ~ r2_hidden(D_207,k1_tarski(A_208))
      | r2_hidden(D_207,k1_ordinal1(A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_182])).

tff(c_1579,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(resolution,[status(thm)],[c_111,c_1565])).

tff(c_70,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_72,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_140,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_78])).

tff(c_60,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_ordinal1(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_80,plain,(
    ! [A_34] :
      ( v1_ordinal1(A_34)
      | ~ v3_ordinal1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_88,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_80])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_602,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,B_111)
      | ~ r2_xboole_0(A_110,B_111)
      | ~ v3_ordinal1(B_111)
      | ~ v1_ordinal1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3565,plain,(
    ! [A_332,B_333] :
      ( r2_hidden(A_332,B_333)
      | ~ v3_ordinal1(B_333)
      | ~ v1_ordinal1(A_332)
      | B_333 = A_332
      | ~ r1_tarski(A_332,B_333) ) ),
    inference(resolution,[status(thm)],[c_22,c_602])).

tff(c_246,plain,(
    ! [D_76,A_77,B_78] :
      ( ~ r2_hidden(D_76,A_77)
      | r2_hidden(D_76,k2_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_407,plain,(
    ! [D_96,A_97] :
      ( ~ r2_hidden(D_96,A_97)
      | r2_hidden(D_96,k1_ordinal1(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_246])).

tff(c_488,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_407,c_98])).

tff(c_3895,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3565,c_488])).

tff(c_4061,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_68,c_3895])).

tff(c_4086,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4061])).

tff(c_4089,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_4086])).

tff(c_4093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_140,c_4089])).

tff(c_4094,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4061])).

tff(c_4099,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4094,c_98])).

tff(c_4105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_4099])).

tff(c_4106,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4107,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_5075,plain,(
    ! [D_445,B_446,A_447] :
      ( r2_hidden(D_445,B_446)
      | r2_hidden(D_445,A_447)
      | ~ r2_hidden(D_445,k2_xboole_0(A_447,B_446)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7226,plain,(
    ! [D_645,A_646] :
      ( r2_hidden(D_645,k1_tarski(A_646))
      | r2_hidden(D_645,A_646)
      | ~ r2_hidden(D_645,k1_ordinal1(A_646)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_5075])).

tff(c_4394,plain,(
    ! [D_387,B_388,A_389] :
      ( D_387 = B_388
      | D_387 = A_389
      | ~ r2_hidden(D_387,k2_tarski(A_389,B_388)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4403,plain,(
    ! [D_387,A_17] :
      ( D_387 = A_17
      | D_387 = A_17
      | ~ r2_hidden(D_387,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4394])).

tff(c_9269,plain,(
    ! [D_721,A_722] :
      ( D_721 = A_722
      | r2_hidden(D_721,A_722)
      | ~ r2_hidden(D_721,k1_ordinal1(A_722)) ) ),
    inference(resolution,[status(thm)],[c_7226,c_4403])).

tff(c_9339,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_4107,c_9269])).

tff(c_9340,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9339])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4647,plain,(
    ! [A_399,B_398] :
      ( ~ r2_hidden(A_399,B_398)
      | r1_ordinal1(A_399,B_398)
      | ~ v3_ordinal1(B_398)
      | ~ v3_ordinal1(A_399) ) ),
    inference(resolution,[status(thm)],[c_4538,c_2])).

tff(c_9343,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9340,c_4647])).

tff(c_9351,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_9343])).

tff(c_9353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4106,c_9351])).

tff(c_9354,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9339])).

tff(c_9359,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9354,c_4106])).

tff(c_9379,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4640,c_9359])).

tff(c_9383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.29/4.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.29/4.11  
% 11.29/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.29/4.12  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 11.29/4.12  
% 11.29/4.12  %Foreground sorts:
% 11.29/4.12  
% 11.29/4.12  
% 11.29/4.12  %Background operators:
% 11.29/4.12  
% 11.29/4.12  
% 11.29/4.12  %Foreground operators:
% 11.29/4.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.29/4.12  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.29/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.29/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.29/4.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.29/4.12  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 11.29/4.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.29/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.29/4.12  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.29/4.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.29/4.12  tff('#skF_5', type, '#skF_5': $i).
% 11.29/4.12  tff('#skF_6', type, '#skF_6': $i).
% 11.29/4.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.29/4.12  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.29/4.12  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 11.29/4.12  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 11.29/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.29/4.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.29/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.29/4.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.29/4.12  
% 11.29/4.14  tff(f_110, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 11.29/4.14  tff(f_95, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 11.29/4.14  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.29/4.14  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.29/4.14  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 11.29/4.14  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.29/4.14  tff(f_69, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 11.29/4.14  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 11.29/4.14  tff(f_77, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.29/4.14  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 11.29/4.14  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 11.29/4.14  tff(f_86, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 11.29/4.14  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 11.29/4.14  tff(c_68, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.29/4.14  tff(c_4538, plain, (![B_398, A_399]: (r2_hidden(B_398, A_399) | r1_ordinal1(A_399, B_398) | ~v3_ordinal1(B_398) | ~v3_ordinal1(A_399))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.29/4.14  tff(c_4190, plain, (![A_357, B_358]: (r1_tarski(k1_tarski(A_357), B_358) | ~r2_hidden(A_357, B_358))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.29/4.14  tff(c_46, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.29/4.14  tff(c_4122, plain, (![D_335, A_336]: (r2_hidden(D_335, k2_tarski(A_336, D_335)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.29/4.14  tff(c_4125, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4122])).
% 11.29/4.14  tff(c_4132, plain, (![B_340, A_341]: (~r1_tarski(B_340, A_341) | ~r2_hidden(A_341, B_340))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.29/4.14  tff(c_4146, plain, (![A_17]: (~r1_tarski(k1_tarski(A_17), A_17))), inference(resolution, [status(thm)], [c_4125, c_4132])).
% 11.29/4.14  tff(c_4195, plain, (![B_358]: (~r2_hidden(B_358, B_358))), inference(resolution, [status(thm)], [c_4190, c_4146])).
% 11.29/4.14  tff(c_4640, plain, (![A_399]: (r1_ordinal1(A_399, A_399) | ~v3_ordinal1(A_399))), inference(resolution, [status(thm)], [c_4538, c_4195])).
% 11.29/4.14  tff(c_108, plain, (![D_37, A_38]: (r2_hidden(D_37, k2_tarski(A_38, D_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.29/4.14  tff(c_111, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_108])).
% 11.29/4.14  tff(c_56, plain, (![A_21]: (k2_xboole_0(A_21, k1_tarski(A_21))=k1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.29/4.14  tff(c_182, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | r2_hidden(D_64, k2_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.29/4.14  tff(c_1565, plain, (![D_207, A_208]: (~r2_hidden(D_207, k1_tarski(A_208)) | r2_hidden(D_207, k1_ordinal1(A_208)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_182])).
% 11.29/4.14  tff(c_1579, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(resolution, [status(thm)], [c_111, c_1565])).
% 11.29/4.14  tff(c_70, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.29/4.14  tff(c_72, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.29/4.14  tff(c_98, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_72])).
% 11.29/4.14  tff(c_78, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.29/4.14  tff(c_140, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_98, c_78])).
% 11.29/4.14  tff(c_60, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~r1_ordinal1(A_22, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.29/4.14  tff(c_80, plain, (![A_34]: (v1_ordinal1(A_34) | ~v3_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.29/4.14  tff(c_88, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_80])).
% 11.29/4.14  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.29/4.14  tff(c_602, plain, (![A_110, B_111]: (r2_hidden(A_110, B_111) | ~r2_xboole_0(A_110, B_111) | ~v3_ordinal1(B_111) | ~v1_ordinal1(A_110))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.29/4.14  tff(c_3565, plain, (![A_332, B_333]: (r2_hidden(A_332, B_333) | ~v3_ordinal1(B_333) | ~v1_ordinal1(A_332) | B_333=A_332 | ~r1_tarski(A_332, B_333))), inference(resolution, [status(thm)], [c_22, c_602])).
% 11.29/4.14  tff(c_246, plain, (![D_76, A_77, B_78]: (~r2_hidden(D_76, A_77) | r2_hidden(D_76, k2_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.29/4.14  tff(c_407, plain, (![D_96, A_97]: (~r2_hidden(D_96, A_97) | r2_hidden(D_96, k1_ordinal1(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_246])).
% 11.29/4.14  tff(c_488, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_407, c_98])).
% 11.29/4.14  tff(c_3895, plain, (~v3_ordinal1('#skF_6') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3565, c_488])).
% 11.29/4.14  tff(c_4061, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_68, c_3895])).
% 11.29/4.14  tff(c_4086, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_4061])).
% 11.29/4.14  tff(c_4089, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_4086])).
% 11.29/4.14  tff(c_4093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_140, c_4089])).
% 11.29/4.14  tff(c_4094, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_4061])).
% 11.29/4.14  tff(c_4099, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4094, c_98])).
% 11.29/4.14  tff(c_4105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1579, c_4099])).
% 11.29/4.14  tff(c_4106, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 11.29/4.14  tff(c_4107, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_72])).
% 11.29/4.14  tff(c_5075, plain, (![D_445, B_446, A_447]: (r2_hidden(D_445, B_446) | r2_hidden(D_445, A_447) | ~r2_hidden(D_445, k2_xboole_0(A_447, B_446)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.29/4.14  tff(c_7226, plain, (![D_645, A_646]: (r2_hidden(D_645, k1_tarski(A_646)) | r2_hidden(D_645, A_646) | ~r2_hidden(D_645, k1_ordinal1(A_646)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_5075])).
% 11.29/4.14  tff(c_4394, plain, (![D_387, B_388, A_389]: (D_387=B_388 | D_387=A_389 | ~r2_hidden(D_387, k2_tarski(A_389, B_388)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.29/4.14  tff(c_4403, plain, (![D_387, A_17]: (D_387=A_17 | D_387=A_17 | ~r2_hidden(D_387, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4394])).
% 11.29/4.14  tff(c_9269, plain, (![D_721, A_722]: (D_721=A_722 | r2_hidden(D_721, A_722) | ~r2_hidden(D_721, k1_ordinal1(A_722)))), inference(resolution, [status(thm)], [c_7226, c_4403])).
% 11.29/4.14  tff(c_9339, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_4107, c_9269])).
% 11.29/4.14  tff(c_9340, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_9339])).
% 11.29/4.14  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.29/4.14  tff(c_4647, plain, (![A_399, B_398]: (~r2_hidden(A_399, B_398) | r1_ordinal1(A_399, B_398) | ~v3_ordinal1(B_398) | ~v3_ordinal1(A_399))), inference(resolution, [status(thm)], [c_4538, c_2])).
% 11.29/4.14  tff(c_9343, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_9340, c_4647])).
% 11.29/4.14  tff(c_9351, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_9343])).
% 11.29/4.14  tff(c_9353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4106, c_9351])).
% 11.29/4.14  tff(c_9354, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_9339])).
% 11.29/4.14  tff(c_9359, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9354, c_4106])).
% 11.29/4.14  tff(c_9379, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_4640, c_9359])).
% 11.29/4.14  tff(c_9383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_9379])).
% 11.29/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.29/4.14  
% 11.29/4.14  Inference rules
% 11.29/4.14  ----------------------
% 11.29/4.14  #Ref     : 0
% 11.29/4.14  #Sup     : 1898
% 11.29/4.14  #Fact    : 12
% 11.29/4.14  #Define  : 0
% 11.29/4.14  #Split   : 6
% 11.29/4.14  #Chain   : 0
% 11.29/4.14  #Close   : 0
% 11.29/4.14  
% 11.29/4.14  Ordering : KBO
% 11.29/4.14  
% 11.29/4.14  Simplification rules
% 11.29/4.14  ----------------------
% 11.29/4.14  #Subsume      : 264
% 11.29/4.14  #Demod        : 41
% 11.29/4.14  #Tautology    : 53
% 11.29/4.14  #SimpNegUnit  : 40
% 11.29/4.14  #BackRed      : 14
% 11.29/4.14  
% 11.29/4.14  #Partial instantiations: 0
% 11.29/4.14  #Strategies tried      : 1
% 11.29/4.14  
% 11.29/4.14  Timing (in seconds)
% 11.29/4.14  ----------------------
% 11.29/4.15  Preprocessing        : 0.51
% 11.29/4.15  Parsing              : 0.25
% 11.29/4.15  CNF conversion       : 0.04
% 11.29/4.15  Main loop            : 2.72
% 11.29/4.15  Inferencing          : 0.75
% 11.29/4.15  Reduction            : 0.78
% 11.29/4.15  Demodulation         : 0.43
% 11.29/4.15  BG Simplification    : 0.11
% 11.29/4.15  Subsumption          : 0.84
% 11.29/4.15  Abstraction          : 0.11
% 11.29/4.15  MUC search           : 0.00
% 11.29/4.15  Cooper               : 0.00
% 11.29/4.15  Total                : 3.29
% 11.29/4.15  Index Insertion      : 0.00
% 11.29/4.15  Index Deletion       : 0.00
% 11.29/4.15  Index Matching       : 0.00
% 11.29/4.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
