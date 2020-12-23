%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0029+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:36 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   29 (  50 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 ( 114 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_544,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_1'(A_74,B_75,C_76),B_75)
      | r2_hidden('#skF_1'(A_74,B_75,C_76),A_74)
      | r2_hidden('#skF_2'(A_74,B_75,C_76),C_76)
      | k2_xboole_0(A_74,B_75) = C_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_947,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95,A_94),B_95)
      | r2_hidden('#skF_2'(A_94,B_95,A_94),A_94)
      | k2_xboole_0(A_94,B_95) = A_94 ) ),
    inference(resolution,[status(thm)],[c_544,c_16])).

tff(c_195,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | r2_hidden('#skF_1'(A_49,B_50,C_51),A_49)
      | ~ r2_hidden('#skF_2'(A_49,B_50,C_51),A_49)
      | k2_xboole_0(A_49,B_50) = C_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_246,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50,A_49),B_50)
      | ~ r2_hidden('#skF_2'(A_49,B_50,A_49),A_49)
      | k2_xboole_0(A_49,B_50) = A_49 ) ),
    inference(resolution,[status(thm)],[c_195,c_12])).

tff(c_998,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97,A_96),B_97)
      | k2_xboole_0(A_96,B_97) = A_96 ) ),
    inference(resolution,[status(thm)],[c_947,c_246])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1211,plain,(
    ! [A_111,A_112,B_113] :
      ( r2_hidden('#skF_1'(A_111,k3_xboole_0(A_112,B_113),A_111),A_112)
      | k2_xboole_0(A_111,k3_xboole_0(A_112,B_113)) = A_111 ) ),
    inference(resolution,[status(thm)],[c_998,c_24])).

tff(c_1406,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_2'(A_128,k3_xboole_0(A_128,B_129),A_128),A_128)
      | k2_xboole_0(A_128,k3_xboole_0(A_128,B_129)) = A_128 ) ),
    inference(resolution,[status(thm)],[c_1211,c_16])).

tff(c_1237,plain,(
    ! [A_112,B_113] :
      ( ~ r2_hidden('#skF_2'(A_112,k3_xboole_0(A_112,B_113),A_112),A_112)
      | k2_xboole_0(A_112,k3_xboole_0(A_112,B_113)) = A_112 ) ),
    inference(resolution,[status(thm)],[c_1211,c_12])).

tff(c_1425,plain,(
    ! [A_128,B_129] : k2_xboole_0(A_128,k3_xboole_0(A_128,B_129)) = A_128 ),
    inference(resolution,[status(thm)],[c_1406,c_1237])).

tff(c_38,plain,(
    k2_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_6')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_38])).

%------------------------------------------------------------------------------
