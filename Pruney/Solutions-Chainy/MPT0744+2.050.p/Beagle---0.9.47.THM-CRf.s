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
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 26.64s
% Output     : CNFRefutation 26.64s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 265 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_132,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_146,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_124,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51893,plain,(
    ! [A_212168,B_212169] :
      ( r1_ordinal1(A_212168,B_212169)
      | ~ r1_tarski(A_212168,B_212169)
      | ~ v3_ordinal1(B_212169)
      | ~ v3_ordinal1(A_212168) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_51902,plain,(
    ! [B_212170] :
      ( r1_ordinal1(B_212170,B_212170)
      | ~ v3_ordinal1(B_212170) ) ),
    inference(resolution,[status(thm)],[c_30,c_51893])).

tff(c_112,plain,(
    ! [B_62] : r2_hidden(B_62,k1_ordinal1(B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_122,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_126,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_132,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_199,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_132])).

tff(c_108,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_ordinal1(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2359,plain,(
    ! [B_321,A_322] :
      ( r2_hidden(B_321,A_322)
      | B_321 = A_322
      | r2_hidden(A_322,B_321)
      | ~ v3_ordinal1(B_321)
      | ~ v3_ordinal1(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_120,plain,(
    ! [B_70,A_69] :
      ( ~ r1_tarski(B_70,A_69)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_49507,plain,(
    ! [B_210967,A_210968] :
      ( ~ r1_tarski(B_210967,A_210968)
      | r2_hidden(B_210967,A_210968)
      | B_210967 = A_210968
      | ~ v3_ordinal1(B_210967)
      | ~ v3_ordinal1(A_210968) ) ),
    inference(resolution,[status(thm)],[c_2359,c_120])).

tff(c_200,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden(A_84,B_85)
      | r2_hidden(A_84,k1_ordinal1(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_207,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_200,c_172])).

tff(c_50211,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_49507,c_207])).

tff(c_50404,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_124,c_50211])).

tff(c_50409,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50404])).

tff(c_50412,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_50409])).

tff(c_50416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_199,c_50412])).

tff(c_50417,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50404])).

tff(c_50425,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50417,c_172])).

tff(c_50429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_50425])).

tff(c_50430,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_51606,plain,(
    ! [B_212137,A_212138] :
      ( r1_ordinal1(B_212137,A_212138)
      | r1_ordinal1(A_212138,B_212137)
      | ~ v3_ordinal1(B_212137)
      | ~ v3_ordinal1(A_212138) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_51107,plain,(
    ! [A_212102,B_212103] :
      ( r1_tarski(A_212102,B_212103)
      | ~ r1_ordinal1(A_212102,B_212103)
      | ~ v3_ordinal1(B_212103)
      | ~ v3_ordinal1(A_212102) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50431,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_50839,plain,(
    ! [B_212071,A_212072] :
      ( B_212071 = A_212072
      | r2_hidden(A_212072,B_212071)
      | ~ r2_hidden(A_212072,k1_ordinal1(B_212071)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50855,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_50431,c_50839])).

tff(c_50858,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50855])).

tff(c_50862,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_50858,c_120])).

tff(c_51124,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_51107,c_50862])).

tff(c_51152,plain,(
    ~ r1_ordinal1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_124,c_51124])).

tff(c_51609,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_51606,c_51152])).

tff(c_51617,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_51609])).

tff(c_51619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50430,c_51617])).

tff(c_51620,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50855])).

tff(c_51624,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51620,c_50430])).

tff(c_51905,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_51902,c_51624])).

tff(c_51909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_51905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.64/17.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.64/17.51  
% 26.64/17.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.64/17.52  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 26.64/17.52  
% 26.64/17.52  %Foreground sorts:
% 26.64/17.52  
% 26.64/17.52  
% 26.64/17.52  %Background operators:
% 26.64/17.52  
% 26.64/17.52  
% 26.64/17.52  %Foreground operators:
% 26.64/17.52  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 26.64/17.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.64/17.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.64/17.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.64/17.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff('#skF_7', type, '#skF_7': $i).
% 26.64/17.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.64/17.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 26.64/17.52  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 26.64/17.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.64/17.52  tff('#skF_6', type, '#skF_6': $i).
% 26.64/17.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 26.64/17.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.64/17.52  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 26.64/17.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.64/17.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 26.64/17.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.64/17.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.64/17.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.64/17.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 26.64/17.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.64/17.52  
% 26.64/17.53  tff(f_156, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 26.64/17.53  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.64/17.53  tff(f_111, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 26.64/17.53  tff(f_117, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 26.64/17.53  tff(f_132, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 26.64/17.53  tff(f_146, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 26.64/17.53  tff(f_101, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 26.64/17.53  tff(c_124, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.64/17.53  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.64/17.53  tff(c_51893, plain, (![A_212168, B_212169]: (r1_ordinal1(A_212168, B_212169) | ~r1_tarski(A_212168, B_212169) | ~v3_ordinal1(B_212169) | ~v3_ordinal1(A_212168))), inference(cnfTransformation, [status(thm)], [f_111])).
% 26.64/17.53  tff(c_51902, plain, (![B_212170]: (r1_ordinal1(B_212170, B_212170) | ~v3_ordinal1(B_212170))), inference(resolution, [status(thm)], [c_30, c_51893])).
% 26.64/17.53  tff(c_112, plain, (![B_62]: (r2_hidden(B_62, k1_ordinal1(B_62)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 26.64/17.53  tff(c_122, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.64/17.53  tff(c_126, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.64/17.53  tff(c_172, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_126])).
% 26.64/17.53  tff(c_132, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.64/17.53  tff(c_199, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_172, c_132])).
% 26.64/17.53  tff(c_108, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~r1_ordinal1(A_59, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_111])).
% 26.64/17.53  tff(c_2359, plain, (![B_321, A_322]: (r2_hidden(B_321, A_322) | B_321=A_322 | r2_hidden(A_322, B_321) | ~v3_ordinal1(B_321) | ~v3_ordinal1(A_322))), inference(cnfTransformation, [status(thm)], [f_132])).
% 26.64/17.53  tff(c_120, plain, (![B_70, A_69]: (~r1_tarski(B_70, A_69) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_146])).
% 26.64/17.53  tff(c_49507, plain, (![B_210967, A_210968]: (~r1_tarski(B_210967, A_210968) | r2_hidden(B_210967, A_210968) | B_210967=A_210968 | ~v3_ordinal1(B_210967) | ~v3_ordinal1(A_210968))), inference(resolution, [status(thm)], [c_2359, c_120])).
% 26.64/17.53  tff(c_200, plain, (![A_84, B_85]: (~r2_hidden(A_84, B_85) | r2_hidden(A_84, k1_ordinal1(B_85)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 26.64/17.53  tff(c_207, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_200, c_172])).
% 26.64/17.53  tff(c_50211, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_49507, c_207])).
% 26.64/17.53  tff(c_50404, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_124, c_50211])).
% 26.64/17.53  tff(c_50409, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50404])).
% 26.64/17.53  tff(c_50412, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_108, c_50409])).
% 26.64/17.53  tff(c_50416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_199, c_50412])).
% 26.64/17.53  tff(c_50417, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_50404])).
% 26.64/17.53  tff(c_50425, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50417, c_172])).
% 26.64/17.53  tff(c_50429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_50425])).
% 26.64/17.53  tff(c_50430, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_126])).
% 26.64/17.53  tff(c_51606, plain, (![B_212137, A_212138]: (r1_ordinal1(B_212137, A_212138) | r1_ordinal1(A_212138, B_212137) | ~v3_ordinal1(B_212137) | ~v3_ordinal1(A_212138))), inference(cnfTransformation, [status(thm)], [f_101])).
% 26.64/17.53  tff(c_51107, plain, (![A_212102, B_212103]: (r1_tarski(A_212102, B_212103) | ~r1_ordinal1(A_212102, B_212103) | ~v3_ordinal1(B_212103) | ~v3_ordinal1(A_212102))), inference(cnfTransformation, [status(thm)], [f_111])).
% 26.64/17.53  tff(c_50431, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_126])).
% 26.64/17.53  tff(c_50839, plain, (![B_212071, A_212072]: (B_212071=A_212072 | r2_hidden(A_212072, B_212071) | ~r2_hidden(A_212072, k1_ordinal1(B_212071)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 26.64/17.53  tff(c_50855, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_50431, c_50839])).
% 26.64/17.53  tff(c_50858, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50855])).
% 26.64/17.53  tff(c_50862, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_50858, c_120])).
% 26.64/17.53  tff(c_51124, plain, (~r1_ordinal1('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_51107, c_50862])).
% 26.64/17.53  tff(c_51152, plain, (~r1_ordinal1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_124, c_51124])).
% 26.64/17.53  tff(c_51609, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_51606, c_51152])).
% 26.64/17.53  tff(c_51617, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_51609])).
% 26.64/17.53  tff(c_51619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50430, c_51617])).
% 26.64/17.53  tff(c_51620, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_50855])).
% 26.64/17.53  tff(c_51624, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_51620, c_50430])).
% 26.64/17.53  tff(c_51905, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_51902, c_51624])).
% 26.64/17.53  tff(c_51909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_51905])).
% 26.64/17.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.64/17.53  
% 26.64/17.53  Inference rules
% 26.64/17.53  ----------------------
% 26.64/17.53  #Ref     : 0
% 26.64/17.53  #Sup     : 8973
% 26.64/17.53  #Fact    : 460
% 26.64/17.53  #Define  : 0
% 26.64/17.53  #Split   : 8
% 26.64/17.53  #Chain   : 0
% 26.64/17.53  #Close   : 0
% 26.64/17.53  
% 26.64/17.53  Ordering : KBO
% 26.64/17.53  
% 26.64/17.53  Simplification rules
% 26.64/17.53  ----------------------
% 26.64/17.53  #Subsume      : 4542
% 26.64/17.53  #Demod        : 94
% 26.64/17.53  #Tautology    : 681
% 26.64/17.53  #SimpNegUnit  : 21
% 26.64/17.53  #BackRed      : 12
% 26.64/17.53  
% 26.64/17.53  #Partial instantiations: 57456
% 26.64/17.53  #Strategies tried      : 1
% 26.64/17.53  
% 26.64/17.53  Timing (in seconds)
% 26.64/17.53  ----------------------
% 27.05/17.53  Preprocessing        : 0.38
% 27.05/17.53  Parsing              : 0.18
% 27.05/17.53  CNF conversion       : 0.03
% 27.05/17.53  Main loop            : 16.39
% 27.05/17.53  Inferencing          : 6.18
% 27.05/17.53  Reduction            : 2.08
% 27.05/17.53  Demodulation         : 1.40
% 27.05/17.53  BG Simplification    : 0.34
% 27.05/17.53  Subsumption          : 7.41
% 27.05/17.53  Abstraction          : 1.13
% 27.05/17.53  MUC search           : 0.00
% 27.05/17.53  Cooper               : 0.00
% 27.05/17.53  Total                : 16.80
% 27.05/17.53  Index Insertion      : 0.00
% 27.05/17.53  Index Deletion       : 0.00
% 27.05/17.53  Index Matching       : 0.00
% 27.05/17.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
