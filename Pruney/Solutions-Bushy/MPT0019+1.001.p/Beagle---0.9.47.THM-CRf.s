%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0019+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:35 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 124 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    k2_xboole_0('#skF_4','#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_512,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden('#skF_2'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_2'(A_99,B_100,C_101),A_99)
      | r2_hidden('#skF_3'(A_99,B_100,C_101),C_101)
      | k2_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_572,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_2'(A_99,B_100,B_100),A_99)
      | r2_hidden('#skF_3'(A_99,B_100,B_100),B_100)
      | k2_xboole_0(A_99,B_100) = B_100 ) ),
    inference(resolution,[status(thm)],[c_512,c_22])).

tff(c_362,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | r2_hidden('#skF_2'(A_81,B_82,C_83),A_81)
      | ~ r2_hidden('#skF_3'(A_81,B_82,C_83),B_82)
      | k2_xboole_0(A_81,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3713,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_2'(A_306,B_307,B_307),A_306)
      | ~ r2_hidden('#skF_3'(A_306,B_307,B_307),B_307)
      | k2_xboole_0(A_306,B_307) = B_307 ) ),
    inference(resolution,[status(thm)],[c_362,c_14])).

tff(c_3776,plain,(
    ! [A_308,B_309] :
      ( r2_hidden('#skF_2'(A_308,B_309,B_309),A_308)
      | k2_xboole_0(A_308,B_309) = B_309 ) ),
    inference(resolution,[status(thm)],[c_572,c_3713])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3843,plain,(
    ! [A_310,B_311,B_312] :
      ( r2_hidden('#skF_2'(A_310,B_311,B_311),B_312)
      | ~ r1_tarski(A_310,B_312)
      | k2_xboole_0(A_310,B_311) = B_311 ) ),
    inference(resolution,[status(thm)],[c_3776,c_2])).

tff(c_3902,plain,(
    ! [A_310,B_312] :
      ( r2_hidden('#skF_3'(A_310,B_312,B_312),B_312)
      | ~ r1_tarski(A_310,B_312)
      | k2_xboole_0(A_310,B_312) = B_312 ) ),
    inference(resolution,[status(thm)],[c_3843,c_22])).

tff(c_4034,plain,(
    ! [A_320,B_321] :
      ( ~ r2_hidden('#skF_3'(A_320,B_321,B_321),B_321)
      | ~ r1_tarski(A_320,B_321)
      | k2_xboole_0(A_320,B_321) = B_321 ) ),
    inference(resolution,[status(thm)],[c_3843,c_14])).

tff(c_4115,plain,(
    ! [A_322,B_323] :
      ( ~ r1_tarski(A_322,B_323)
      | k2_xboole_0(A_322,B_323) = B_323 ) ),
    inference(resolution,[status(thm)],[c_3902,c_4034])).

tff(c_4172,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_4115])).

tff(c_4195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4172])).

%------------------------------------------------------------------------------
