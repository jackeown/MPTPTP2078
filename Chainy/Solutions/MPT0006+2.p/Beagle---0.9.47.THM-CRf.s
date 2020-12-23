%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  81 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_17 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_106,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_203,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,B)
                & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_108,plain,(
    ! [A_48] : ~ r2_xboole_0(A_48,A_48) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_977,plain,(
    ! [A_184,B_185] :
      ( r2_xboole_0(A_184,B_185)
      | B_185 = A_184
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_188,plain,(
    r2_xboole_0('#skF_17','#skF_18') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_277,plain,(
    ! [B_88,A_89] :
      ( ~ r2_xboole_0(B_88,A_89)
      | ~ r2_xboole_0(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_280,plain,(
    ~ r2_xboole_0('#skF_18','#skF_17') ),
    inference(resolution,[status(thm)],[c_188,c_277])).

tff(c_991,plain,
    ( '#skF_18' = '#skF_17'
    | ~ r1_tarski('#skF_18','#skF_17') ),
    inference(resolution,[status(thm)],[c_977,c_280])).

tff(c_995,plain,(
    ~ r1_tarski('#skF_18','#skF_17') ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_762,plain,(
    ! [A_155,B_156] :
      ( r2_hidden('#skF_2'(A_155,B_156),A_155)
      | r1_tarski(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [C_77] :
      ( r2_hidden(C_77,'#skF_17')
      | ~ r2_hidden(C_77,'#skF_18') ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_774,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_2'('#skF_18',B_156),'#skF_17')
      | r1_tarski('#skF_18',B_156) ) ),
    inference(resolution,[status(thm)],[c_762,c_186])).

tff(c_1371,plain,(
    ! [A_221,B_222] :
      ( ~ r2_hidden('#skF_2'(A_221,B_222),B_222)
      | r1_tarski(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1379,plain,(
    r1_tarski('#skF_18','#skF_17') ),
    inference(resolution,[status(thm)],[c_774,c_1371])).

tff(c_1392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_995,c_995,c_1379])).

tff(c_1393,plain,(
    '#skF_18' = '#skF_17' ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_1406,plain,(
    r2_xboole_0('#skF_17','#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_188])).

tff(c_1408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_1406])).
%------------------------------------------------------------------------------
