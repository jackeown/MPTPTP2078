%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:09 EST 2020

% Result     : Theorem 13.75s
% Output     : CNFRefutation 14.03s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 290 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 752 expanded)
%              Number of equality atoms :   17 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_88,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    ! [A_27] :
      ( v3_ordinal1(k1_ordinal1(A_27))
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_486,plain,(
    ! [B_101,A_102] :
      ( r2_hidden(B_101,A_102)
      | r1_ordinal1(A_102,B_101)
      | ~ v3_ordinal1(B_101)
      | ~ v3_ordinal1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_92,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_58])).

tff(c_565,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_486,c_109])).

tff(c_597,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_565])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_ordinal1(A_20,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_756,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(A_123,B_124)
      | ~ r1_ordinal1(A_123,B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2858,plain,(
    ! [B_297,A_298] :
      ( B_297 = A_298
      | ~ r1_tarski(B_297,A_298)
      | ~ r1_ordinal1(A_298,B_297)
      | ~ v3_ordinal1(B_297)
      | ~ v3_ordinal1(A_298) ) ),
    inference(resolution,[status(thm)],[c_756,c_22])).

tff(c_18363,plain,(
    ! [B_1679,A_1680] :
      ( B_1679 = A_1680
      | ~ r1_ordinal1(B_1679,A_1680)
      | ~ r1_ordinal1(A_1680,B_1679)
      | ~ v3_ordinal1(B_1679)
      | ~ v3_ordinal1(A_1680) ) ),
    inference(resolution,[status(thm)],[c_40,c_2858])).

tff(c_18381,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_597,c_18363])).

tff(c_18400,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_18381])).

tff(c_18480,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18400])).

tff(c_48,plain,(
    ! [B_26,A_24] :
      ( r2_hidden(B_26,A_24)
      | r1_ordinal1(A_24,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18389,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_18363])).

tff(c_18407,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18389])).

tff(c_18493,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18407])).

tff(c_18496,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_18493])).

tff(c_18500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18496])).

tff(c_18502,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18407])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | r2_hidden(A_22,k1_ordinal1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1918,plain,(
    ! [A_235,B_236] :
      ( ~ r2_hidden(A_235,B_236)
      | r1_ordinal1(A_235,B_236)
      | ~ v3_ordinal1(B_236)
      | ~ v3_ordinal1(A_235) ) ),
    inference(resolution,[status(thm)],[c_486,c_2])).

tff(c_18506,plain,(
    ! [A_1685,B_1686] :
      ( r1_ordinal1(A_1685,k1_ordinal1(B_1686))
      | ~ v3_ordinal1(k1_ordinal1(B_1686))
      | ~ v3_ordinal1(A_1685)
      | ~ r2_hidden(A_1685,B_1686) ) ),
    inference(resolution,[status(thm)],[c_46,c_1918])).

tff(c_18501,plain,
    ( ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | k1_ordinal1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18407])).

tff(c_18503,plain,(
    ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18501])).

tff(c_18509,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18506,c_18503])).

tff(c_18522,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18502,c_18509])).

tff(c_18528,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_18522])).

tff(c_18531,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_18528])).

tff(c_18533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18480,c_18531])).

tff(c_18534,plain,(
    k1_ordinal1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18501])).

tff(c_44,plain,(
    ! [B_23] : r2_hidden(B_23,k1_ordinal1(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    ! [B_39,A_40] :
      ( ~ r1_tarski(B_39,A_40)
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_97,plain,(
    ! [B_23] : ~ r1_tarski(k1_ordinal1(B_23),B_23) ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_783,plain,(
    ! [B_124] :
      ( ~ r1_ordinal1(k1_ordinal1(B_124),B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(k1_ordinal1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_756,c_97])).

tff(c_19355,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18534,c_783])).

tff(c_19493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18534,c_56,c_597,c_19355])).

tff(c_19494,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18400])).

tff(c_19498,plain,(
    r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19494,c_92])).

tff(c_19516,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19498,c_783])).

tff(c_19522,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_19516])).

tff(c_19526,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_19522])).

tff(c_19530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_19526])).

tff(c_19531,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_19535,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_19531,c_2])).

tff(c_19956,plain,(
    ! [B_1755,A_1756] :
      ( r1_ordinal1(B_1755,A_1756)
      | r1_ordinal1(A_1756,B_1755)
      | ~ v3_ordinal1(B_1755)
      | ~ v3_ordinal1(A_1756) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19532,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_19959,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19956,c_19532])).

tff(c_19965,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_19959])).

tff(c_19970,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19965])).

tff(c_19973,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_19970])).

tff(c_19977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_19973])).

tff(c_19979,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19965])).

tff(c_19980,plain,(
    ! [B_1758,A_1759] :
      ( r2_hidden(B_1758,A_1759)
      | r1_ordinal1(A_1759,B_1758)
      | ~ v3_ordinal1(B_1758)
      | ~ v3_ordinal1(A_1759) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( B_23 = A_22
      | r2_hidden(A_22,B_23)
      | ~ r2_hidden(A_22,k1_ordinal1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22491,plain,(
    ! [B_1968,B_1967] :
      ( B_1968 = B_1967
      | r2_hidden(B_1968,B_1967)
      | r1_ordinal1(k1_ordinal1(B_1967),B_1968)
      | ~ v3_ordinal1(B_1968)
      | ~ v3_ordinal1(k1_ordinal1(B_1967)) ) ),
    inference(resolution,[status(thm)],[c_19980,c_42])).

tff(c_22498,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22491,c_19532])).

tff(c_22503,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19979,c_54,c_22498])).

tff(c_22504,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_19535,c_22503])).

tff(c_19536,plain,(
    ! [B_1691,A_1692] :
      ( ~ r1_tarski(B_1691,A_1692)
      | ~ r2_hidden(A_1692,B_1691) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19543,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_19531,c_19536])).

tff(c_22509,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22504,c_19543])).

tff(c_22516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.75/6.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/6.15  
% 13.75/6.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/6.15  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 13.75/6.15  
% 13.75/6.15  %Foreground sorts:
% 13.75/6.15  
% 13.75/6.15  
% 13.75/6.15  %Background operators:
% 13.75/6.15  
% 13.75/6.15  
% 13.75/6.15  %Foreground operators:
% 13.75/6.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.75/6.15  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 13.75/6.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.75/6.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.75/6.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.75/6.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.75/6.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.75/6.15  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 13.75/6.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.75/6.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.75/6.15  tff('#skF_3', type, '#skF_3': $i).
% 13.75/6.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.75/6.15  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 13.75/6.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.75/6.15  tff('#skF_4', type, '#skF_4': $i).
% 13.75/6.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.75/6.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.75/6.15  
% 14.03/6.17  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.03/6.17  tff(f_103, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 14.03/6.17  tff(f_88, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 14.03/6.17  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 14.03/6.17  tff(f_69, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 14.03/6.17  tff(f_75, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 14.03/6.17  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 14.03/6.17  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.03/6.17  tff(f_59, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 14.03/6.17  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.03/6.17  tff(c_54, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.03/6.17  tff(c_50, plain, (![A_27]: (v3_ordinal1(k1_ordinal1(A_27)) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.03/6.17  tff(c_56, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.03/6.17  tff(c_486, plain, (![B_101, A_102]: (r2_hidden(B_101, A_102) | r1_ordinal1(A_102, B_101) | ~v3_ordinal1(B_101) | ~v3_ordinal1(A_102))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.03/6.17  tff(c_64, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.03/6.17  tff(c_92, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 14.03/6.17  tff(c_58, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.03/6.17  tff(c_109, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_58])).
% 14.03/6.17  tff(c_565, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_486, c_109])).
% 14.03/6.17  tff(c_597, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_565])).
% 14.03/6.17  tff(c_40, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~r1_ordinal1(A_20, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.03/6.17  tff(c_756, plain, (![A_123, B_124]: (r1_tarski(A_123, B_124) | ~r1_ordinal1(A_123, B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1(A_123))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.03/6.17  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.03/6.17  tff(c_2858, plain, (![B_297, A_298]: (B_297=A_298 | ~r1_tarski(B_297, A_298) | ~r1_ordinal1(A_298, B_297) | ~v3_ordinal1(B_297) | ~v3_ordinal1(A_298))), inference(resolution, [status(thm)], [c_756, c_22])).
% 14.03/6.17  tff(c_18363, plain, (![B_1679, A_1680]: (B_1679=A_1680 | ~r1_ordinal1(B_1679, A_1680) | ~r1_ordinal1(A_1680, B_1679) | ~v3_ordinal1(B_1679) | ~v3_ordinal1(A_1680))), inference(resolution, [status(thm)], [c_40, c_2858])).
% 14.03/6.17  tff(c_18381, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_597, c_18363])).
% 14.03/6.17  tff(c_18400, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_18381])).
% 14.03/6.17  tff(c_18480, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_18400])).
% 14.03/6.17  tff(c_48, plain, (![B_26, A_24]: (r2_hidden(B_26, A_24) | r1_ordinal1(A_24, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.03/6.17  tff(c_18389, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_18363])).
% 14.03/6.17  tff(c_18407, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18389])).
% 14.03/6.17  tff(c_18493, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_18407])).
% 14.03/6.17  tff(c_18496, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_18493])).
% 14.03/6.17  tff(c_18500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_18496])).
% 14.03/6.17  tff(c_18502, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_18407])).
% 14.03/6.17  tff(c_46, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | r2_hidden(A_22, k1_ordinal1(B_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.03/6.17  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.03/6.17  tff(c_1918, plain, (![A_235, B_236]: (~r2_hidden(A_235, B_236) | r1_ordinal1(A_235, B_236) | ~v3_ordinal1(B_236) | ~v3_ordinal1(A_235))), inference(resolution, [status(thm)], [c_486, c_2])).
% 14.03/6.17  tff(c_18506, plain, (![A_1685, B_1686]: (r1_ordinal1(A_1685, k1_ordinal1(B_1686)) | ~v3_ordinal1(k1_ordinal1(B_1686)) | ~v3_ordinal1(A_1685) | ~r2_hidden(A_1685, B_1686))), inference(resolution, [status(thm)], [c_46, c_1918])).
% 14.03/6.17  tff(c_18501, plain, (~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | k1_ordinal1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_18407])).
% 14.03/6.17  tff(c_18503, plain, (~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_18501])).
% 14.03/6.17  tff(c_18509, plain, (~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18506, c_18503])).
% 14.03/6.17  tff(c_18522, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18502, c_18509])).
% 14.03/6.17  tff(c_18528, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_18522])).
% 14.03/6.17  tff(c_18531, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_18528])).
% 14.03/6.17  tff(c_18533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18480, c_18531])).
% 14.03/6.17  tff(c_18534, plain, (k1_ordinal1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_18501])).
% 14.03/6.17  tff(c_44, plain, (![B_23]: (r2_hidden(B_23, k1_ordinal1(B_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.03/6.17  tff(c_93, plain, (![B_39, A_40]: (~r1_tarski(B_39, A_40) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.03/6.17  tff(c_97, plain, (![B_23]: (~r1_tarski(k1_ordinal1(B_23), B_23))), inference(resolution, [status(thm)], [c_44, c_93])).
% 14.03/6.17  tff(c_783, plain, (![B_124]: (~r1_ordinal1(k1_ordinal1(B_124), B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1(k1_ordinal1(B_124)))), inference(resolution, [status(thm)], [c_756, c_97])).
% 14.03/6.17  tff(c_19355, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18534, c_783])).
% 14.03/6.17  tff(c_19493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_18534, c_56, c_597, c_19355])).
% 14.03/6.17  tff(c_19494, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_18400])).
% 14.03/6.17  tff(c_19498, plain, (r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19494, c_92])).
% 14.03/6.17  tff(c_19516, plain, (~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_19498, c_783])).
% 14.03/6.17  tff(c_19522, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_19516])).
% 14.03/6.17  tff(c_19526, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_19522])).
% 14.03/6.17  tff(c_19530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_19526])).
% 14.03/6.17  tff(c_19531, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 14.03/6.17  tff(c_19535, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_19531, c_2])).
% 14.03/6.17  tff(c_19956, plain, (![B_1755, A_1756]: (r1_ordinal1(B_1755, A_1756) | r1_ordinal1(A_1756, B_1755) | ~v3_ordinal1(B_1755) | ~v3_ordinal1(A_1756))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.03/6.17  tff(c_19532, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 14.03/6.17  tff(c_19959, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_19956, c_19532])).
% 14.03/6.17  tff(c_19965, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_19959])).
% 14.03/6.17  tff(c_19970, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_19965])).
% 14.03/6.17  tff(c_19973, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_19970])).
% 14.03/6.17  tff(c_19977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_19973])).
% 14.03/6.17  tff(c_19979, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_19965])).
% 14.03/6.17  tff(c_19980, plain, (![B_1758, A_1759]: (r2_hidden(B_1758, A_1759) | r1_ordinal1(A_1759, B_1758) | ~v3_ordinal1(B_1758) | ~v3_ordinal1(A_1759))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.03/6.17  tff(c_42, plain, (![B_23, A_22]: (B_23=A_22 | r2_hidden(A_22, B_23) | ~r2_hidden(A_22, k1_ordinal1(B_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.03/6.17  tff(c_22491, plain, (![B_1968, B_1967]: (B_1968=B_1967 | r2_hidden(B_1968, B_1967) | r1_ordinal1(k1_ordinal1(B_1967), B_1968) | ~v3_ordinal1(B_1968) | ~v3_ordinal1(k1_ordinal1(B_1967)))), inference(resolution, [status(thm)], [c_19980, c_42])).
% 14.03/6.17  tff(c_22498, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_22491, c_19532])).
% 14.03/6.17  tff(c_22503, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19979, c_54, c_22498])).
% 14.03/6.17  tff(c_22504, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_19535, c_22503])).
% 14.03/6.17  tff(c_19536, plain, (![B_1691, A_1692]: (~r1_tarski(B_1691, A_1692) | ~r2_hidden(A_1692, B_1691))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.03/6.17  tff(c_19543, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_19531, c_19536])).
% 14.03/6.17  tff(c_22509, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22504, c_19543])).
% 14.03/6.17  tff(c_22516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22509])).
% 14.03/6.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.03/6.17  
% 14.03/6.17  Inference rules
% 14.03/6.17  ----------------------
% 14.03/6.17  #Ref     : 0
% 14.03/6.17  #Sup     : 4957
% 14.03/6.17  #Fact    : 16
% 14.03/6.17  #Define  : 0
% 14.03/6.17  #Split   : 5
% 14.03/6.17  #Chain   : 0
% 14.03/6.17  #Close   : 0
% 14.03/6.17  
% 14.03/6.17  Ordering : KBO
% 14.03/6.17  
% 14.03/6.17  Simplification rules
% 14.03/6.17  ----------------------
% 14.03/6.17  #Subsume      : 1676
% 14.03/6.17  #Demod        : 156
% 14.03/6.17  #Tautology    : 90
% 14.03/6.17  #SimpNegUnit  : 99
% 14.03/6.17  #BackRed      : 16
% 14.03/6.17  
% 14.03/6.17  #Partial instantiations: 0
% 14.03/6.17  #Strategies tried      : 1
% 14.03/6.17  
% 14.03/6.17  Timing (in seconds)
% 14.03/6.17  ----------------------
% 14.03/6.17  Preprocessing        : 0.32
% 14.03/6.17  Parsing              : 0.16
% 14.03/6.17  CNF conversion       : 0.02
% 14.03/6.17  Main loop            : 5.07
% 14.03/6.17  Inferencing          : 0.82
% 14.03/6.17  Reduction            : 1.21
% 14.03/6.17  Demodulation         : 0.55
% 14.03/6.17  BG Simplification    : 0.09
% 14.03/6.17  Subsumption          : 2.64
% 14.03/6.17  Abstraction          : 0.11
% 14.03/6.17  MUC search           : 0.00
% 14.03/6.17  Cooper               : 0.00
% 14.03/6.17  Total                : 5.42
% 14.03/6.17  Index Insertion      : 0.00
% 14.03/6.17  Index Deletion       : 0.00
% 14.03/6.17  Index Matching       : 0.00
% 14.03/6.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
